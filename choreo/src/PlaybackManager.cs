using System;
using System.Collections.Generic;
using System.Linq;
using Dalamud.Plugin.Services;

namespace ChoreoHelper;

public sealed class PlaybackManager : IDisposable
{
    private readonly IPluginLog _log;
    private readonly IFramework _framework;
    private readonly GameCommandExecutor _executor;
    private readonly AnimationPoseFreezer _freezer;

    private List<PlaybackClip> _clips = new();
    private float _currentTime = 0;
    private bool _isPlaying = false;
    private float _speed = 1.0f;
    private HashSet<int> _executedClipIds = new();
    private readonly object _stateLock = new();   // 保护播放状态：HTTP 线程(Play/Stop/Seek)与游戏线程(Update)并发访问
    private long _lastUpdateTick;                  // 单调时钟(Environment.TickCount64)，避免 DateTime.Now 受改时影响
    private float _maxEnd;                         // 时间轴总长，SetTimeline 时缓存，避免每帧 LINQ
    private int _lastSeekClipId = -1;      // 上次 seek 执行的动作，防止重复执行同一动作
    private const float PlaybackLead = 0.5f; // 播放提前量：补偿命令队列(200ms 节流)+游戏动画启动延迟，否则动作比时间轴偏晚

    public bool IsPlaying => _isPlaying;
    public float CurrentTime => _currentTime;

    public PlaybackManager(IPluginLog log, IFramework framework, GameCommandExecutor executor, AnimationPoseFreezer freezer)
    {
        _log = log;
        _framework = framework;
        _executor = executor;
        _freezer = freezer;
        _framework.Update += OnFrameworkUpdate;
    }

    private void OnFrameworkUpdate(IFramework framework)
    {
        lock (_stateLock)
        {
            if (!_isPlaying) return;

            var now = Environment.TickCount64;
            var delta = (float)(now - _lastUpdateTick) / 1000f * _speed;
            _lastUpdateTick = now;
            _currentTime += delta;

            foreach (var clip in _clips)
            {
                if (_executedClipIds.Contains(clip.Id)) continue;
                // 提前量发送：命令要过执行队列+游戏动画启动，到点才发必然偏晚；
                // 提前 PlaybackLead 发出，让动画实际起播时刻对上时间轴位置
                if (clip.Start <= _currentTime + PlaybackLead)
                {
                    ExecuteClip(clip);
                    _executedClipIds.Add(clip.Id);
                }
            }

            if (_currentTime >= _maxEnd)
            {
                _isPlaying = false;
                _currentTime = _maxEnd;
                _executor.Clear();   // 结束清空残留命令，防止停止后角色乱动
                _freezer.StopPreview();
                _log.Information("Playback finished at {time}s", _currentTime);
            }
        }
    }

    private void ExecuteClip(PlaybackClip clip)
    {
        try
        {
            if (string.IsNullOrEmpty(clip.Command)) return;
            _executor.ExecuteCommand(clip.Command);
            _log.Information("Executed at {time}s: {cmd}", clip.Start, clip.Command);
        }
        catch (Exception ex)
        {
            _log.Error(ex, "ExecuteClip failed at {time}s", clip.Start);
        }
    }

    public void SetTimeline(List<PlaybackClip> clips)
    {
        lock (_stateLock)
        {
            _clips = clips.OrderBy(c => c.Start).ToList();
            _maxEnd = _clips.Count > 0 ? _clips.Max(c => c.Start + c.Duration) : 0;
            _executedClipIds.Clear();
            _lastSeekClipId = -1;
            _log.Information("Timeline set with {count} clips, maxEnd={maxEnd}s", _clips.Count, _maxEnd);
        }
    }

    public void SetSpeed(float speed) => _speed = Math.Clamp(speed, 0.25f, 2.0f);

    public void Play(float fromTime = -1)
    {
        lock (_stateLock)
        {
            if (_clips.Count == 0) return;
            // 播放中重复无参 Play：忽略（防止前端双击/连点导致重置重播）
            if (_isPlaying && fromTime < 0) return;
            _freezer.StopPreview(); // 播放与定格互斥：退出定格，让角色自由表演
            _executor.Clear();       // 清空上一轮残留命令
            _executedClipIds.Clear();
            _lastSeekClipId = -1;
            if (fromTime >= 0)
            {
                _currentTime = fromTime;
            }
            else if (_currentTime >= _maxEnd)
            {
                _currentTime = 0; // 播完后再点播放：从头开始
            }
            // 无论从头/指定点/暂停恢复：已完全结束的动作都标记为已执行，
            // 否则恢复播放的瞬间会把整串历史命令补发出去（200ms 节流下卡成一片）；
            // 正在播放中的动作（start <= t < start+duration）不标记，恢复时它会重新执行
            foreach (var clip in _clips)
            {
                if (clip.Start + clip.Duration <= _currentTime) _executedClipIds.Add(clip.Id);
            }
            _lastUpdateTick = Environment.TickCount64;
            _isPlaying = true;
            _log.Information("Playback started from {time}s", _currentTime);
        }
    }

    public void Pause()
    {
        lock (_stateLock)
        {
            _isPlaying = false;
            _executor.Clear();
            _freezer.StopPreview();
            _log.Information("Playback paused at {time}s", _currentTime);
        }
    }

    public void Stop()
    {
        lock (_stateLock)
        {
            _isPlaying = false;
            _currentTime = 0;
            _executedClipIds.Clear();
            _lastSeekClipId = -1;
            _executor.Clear(); // 停止立即清空队列：防止残留命令继续执行/混入下次播放
            _freezer.StopPreview();
            _log.Information("Playback stopped");
        }
    }

    /// <summary>
    /// 预览式 Seek：跳到 t 时刻，并执行"该时刻正在播放"的动作。
    /// 如果 t 落在某个动作的区间内 [start, start+duration)，重新执行该动作，
    /// 角色会从头播放这个动作 —— 用户就能看到这个动作在该时刻的姿态/进度。
    /// </summary>
    public void Seek(float time)
    {
        lock (_stateLock)
        {
            SeekLocked(time);
        }
    }

    private void SeekLocked(float time)
    {
        _currentTime = Math.Max(0, time);
        _isPlaying = false;
        _executedClipIds.Clear();
        _lastSeekClipId = -1;
        // 注意：这里不能 _executor.Clear() —— 定格器刚入队的动作命令可能还没过 200ms 节流，
        // 后续同动作的 seek（拖动时每 50ms 一发）会把它清掉，导致动作永远不执行（漏动作）。
        // 清队列由定格器在"命令切换"时自行处理。
        foreach (var clip in _clips)
        {
            if (clip.Start < _currentTime) _executedClipIds.Add(clip.Id);
        }

        // P2 修复：去掉后端 150ms 节流 —— 前端已有 150ms 节流 + 在途合并，
        // 后端再节流并丢弃最新位置会导致"拖到哪停就停在旧姿态"（最坏 ~300ms 不更新）。
        // 重复执行由 Freezer 的同命令 1.5s 去重挡住，这里每次都处理最新位置。

        // 找到 t 时刻"正在播放"的动作：start <= t < start+duration
        // 定格预览：执行该动作，并把动画时间拨到 (t - start) 秒 —— 角色显示该时刻的姿态
        PlaybackClip? active = null;
        foreach (var clip in _clips)
        {
            if (clip.Start <= _currentTime + 0.05f)
            {
                if (_currentTime < clip.Start + Math.Max(clip.Duration, 0.5f))
                {
                    active = clip; // 正在播放区间内，取最新的一个
                }
                // P4 修复：删掉"兜底取最近开始的已结束 clip"分支 ——
                // t 落在两个动作空隙时应无动作（StopPreview），而不是重播上一个已结束的动作
            }
            else break;
        }

        if (active != null)
        {
            _lastSeekClipId = active.Id;
            // 动作开始时刻 + 已播放时长 = 目标动画时间
            var inClipTime = Math.Max(0, _currentTime - active.Start);
            // 只对动作类做定格；台词/切换类直接执行
            if (active.Type == "action" || active.Type == "switch")
            {
                _freezer.RequestFreezePreview(active.Command, inClipTime);
                _log.Information("Seek freeze at {time}s -> {cmd} (anim t={t}s)", _currentTime, active.Command, inClipTime);
            }
            else
            {
                ExecuteClip(active);
            }
        }
        else
        {
            _freezer.RequestStopPreview(); // 拖动流中的空隙也要延迟停止（立即恢复速度会让旧动画在拖动中乱播）
            _log.Information("Seeked to {time}s (no active clip)", _currentTime);
        }
    }

    public void Dispose()
    {
        _framework.Update -= OnFrameworkUpdate;
    }
}

public sealed class PlaybackClip
{
    public int Id { get; set; }
    public float Start { get; set; }
    public float Duration { get; set; }
    public string Command { get; set; } = "";
    public string Type { get; set; } = "";
    public string Name { get; set; } = "";
}
