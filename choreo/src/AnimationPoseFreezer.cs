using System;
using System.Collections.Concurrent;
using Dalamud.Plugin.Services;
using FFXIVClientStructs.FFXIV.Client.Game.Character;
using FFXIVClientStructs.FFXIV.Client.Graphics.Scene;
using Lumina.Excel.Sheets;

namespace ChoreoHelper;

/// <summary>
/// 动画定格器：把角色当前动画的播放时间(LocalTime)拨到指定秒数并持续保持。
/// 用于"拖动时间轴 → 角色定格在某个动作的某个时刻"的实时预览。
/// 槽位访问参考 SimpleHeels DoEmoteSync：character->DrawObject(Human)->Skeleton->PartialSkeletons[0]->GetHavokAnimatedSkeleton(0)->AnimationControls[0]
/// v0.5.5（修"部分动作抽搐+停不住"）：
///  - 三层停表防御：只冻结主控制槽不可靠 —— 游戏每帧会重算/覆盖各槽速度（Brio 为此专门
///    hook 了 CalculateAndApplyOverallSpeed），被覆盖后动画偷偷推进到结尾 → 游戏判动作结束
///    换绑 → 自愈重播 → 循环（表现为"停不住"+"抽搐"）。现在：
///    1) Timeline.OverallSpeed=0（Brio 同款字段：游戏自己把整体速度应用到所有槽+粒子）
///    2) 全部控制槽 PlaybackSpeed=0（伴随槽不冻结会继续动/触发结束判定）
///    3) 主槽 LocalTime 漂移校正：速度被覆盖时按需拉回（>30ms 才写，不每帧对抗）
///  - 挂载验证接受表情的全部时间轴变体（部分动作实际绑定的不是 ActionTimeline[0]，
///    单 id 验证永不通过 → 永不钉时间 = "停不住"）
/// v0.5.4：
///  - 表情命令走 EmoteManager.ExecuteEmote 直接通道（即时、无聊天节流、状态机注册、不刷聊天）
///  - GetSlotTimeline(0) 确定性挂载验证；根治回拖盲挂旧动画（错误动作）
/// v0.5.3 保留：H1 移动锚点解除；H2 切图清理；自愈换绑；LocalTime 钳制；按变化写入
/// </summary>
public unsafe sealed class AnimationPoseFreezer : IDisposable
{
    private readonly IPluginLog _log;
    private readonly IObjectTable _objectTable;
    private readonly IFramework _framework;
    private readonly GameCommandExecutor _executor;
    private readonly IDataManager _dataManager;

    private readonly struct EmoteIds
    {
        public readonly ushort Emote;
        public readonly ushort[] Timelines;
        public readonly bool AnyLoop;
        public readonly ushort[] EmoteFamily; // 同 TextCommand 的全部表情行号（游戏实际执行的可能是任何变体行）
        public readonly bool IsFacial;        // 表情分类（category=="表情"）：动画在面部骨架不绑主槽0，免定格流程
        public EmoteIds(ushort emote, ushort[] timelines, bool anyLoop, ushort[] family, bool facial)
        { Emote = emote; Timelines = timelines; AnyLoop = anyLoop; EmoteFamily = family; IsFacial = facial; }
    }

    // 运行时学习的实际时间轴：舞蹈等动作走变体机制，实际绑定的槽0时间轴 id 不在
    // Emote 表 ActionTimeline[0..5] 里（如 /breakdance 实际绑 7407）——首次观察到即学习，
    // 之后验证直接通过（不然重试 8 次也挂不上 = "停不住"）
    private static readonly ConcurrentDictionary<string, List<ushort>> LearnedTimelines = new();

    // 待机时间轴 id 集合（学习排除）：过渡窗口里"EmoteId 已是新表情但动画还没绑上"时
    // 槽0 是待机 —— 学习路径会把待机 id 学进缓存（曾实际发生：learned timeline 3）。
    // 污染后该表情永远验证"通过"并钉在待机上 = 吞动作；且越拖污染越多。
    private readonly HashSet<ushort> _idleTimelines = new();
    private double _lastIdleObserve;
    private ushort _learnCandidate;      // 学习路径 C 的候选 id（连续稳定帧计数）
    private int _learnCandidateFrames;
    private ushort _residualCandidate;   // 残留确认学习的候选 id（连续稳定帧计数）
    private int _residualCandidateFrames;
    private ushort _motionSentSlot0 = ushort.MaxValue; // 每条 motion 命令发出时刻的槽0快照：
    // motion 生效的证据是槽0变成"≠发出时的值"。等待期槽0=待机(3)且与快照相同 → 不是 motion 的产物，
    // 绝不能学（曾把待机 3 学进缓存 → 之后永远挂待机 = 吞动作）
    private ushort _playedTimelineId;   // 本轮通过 PlayActionTimeline 直接强制的时间轴 id（0=未用该通道）
    private int _playIdx;               // PlayTimeline 重试的候选轮换索引（失败换族内下一个 id）
    private string _execChannel = "";   // 本轮执行通道（learned/emote/motion，日志用）
    private bool _facialOnly;           // 面部表情类：动画在面部骨架不绑主槽0 —— 执行确认即完成，不进主槽定格
    private double _execStartedAt;      // 本轮执行发起时刻（不随 retry 重置 —— 面部类判定需要跨越 retry 的稳定计时）
    private bool _gaveUp;               // 有界放弃：命令已发完仍未挂载，静默等待（防无限兜底命令风暴）
    private bool _lastWasLoop;          // 上个执行的是循环姿态型动作（坐地/躺椅等）—— 切换时需强制解除

    // 命令的执行通道偏好：ExecuteEmote 被游戏拒绝的表情（如 breakdance）由 motion 兜底
    // 挂载后记住 —— 之后直接走 motion 通道，省去每次 0.5-1s 的无效 ExecuteEmote 尝试
    private static readonly ConcurrentDictionary<string, bool> MotionPreferred = new();

    // 命令已确认的挂载动画时长：变体 id 不止一个（如 breakdance 有 7406/7407），学习只记住
    // 遇到过的 —— 其他变体验证不过（动画明明在播却不挂 = 吞动作观感）。时长是变体族的不变量，
    // 绑定时长与已确认值一致（±0.15s）即认定为同动画的另一变体
    private static readonly ConcurrentDictionary<string, float> KnownAttachDurations = new();

    // 当前"定格预览"状态
    private bool _previewMode;
    private string? _pendingCommand;
    private float _pendingTime;

    // 上次执行的定格命令；命令变化或动作被游戏结束时才重新执行
    private string? _lastCommand;

    // 直接表情通道（表情命令）：命令 → 表情行ID + 全部时间轴行ID
    private static ConcurrentDictionary<string, EmoteIds>? _emoteMap;
    private ushort[] _awaitTimelineIds = Array.Empty<ushort>(); // 等待挂载的时间轴集合（空=聊天通道）
    private ushort _awaitEmoteId;      // 对应的表情行ID（重试用）
    private ushort[] _awaitEmoteFamily = Array.Empty<ushort>(); // 同命令全部表情行号（状态机确认用族匹配）
    private bool _awaitIsLoop;         // 该表情含循环时间轴（定格目标时间需按单轮时长取模）
    private ushort _preExecSlot0;      // 执行前的槽0时间轴 id（学习实际绑定用：重试后变成且稳定的值=该表情实际绑定）
    private int _directAttempts;       // 直接通道重试次数
    private int _chatRetries;          // 聊天通道超时重发次数

    // 挂载状态：_attached=false 时轮询等待新动画绑定到控制槽
    private bool _attached;
    private float _preExecDuration = -1f; // 执行命令前槽上绑定的动画时长（旧动作/待机）
    private long _preExecBinding;         // 执行命令前的绑定指针
    private float _attachDuration = -1f;  // 挂载的动画真实时长（用于检测游戏换绑回待机）
    private long _attachBinding;          // 挂载时的绑定指针（指针变化=换绑，比时长更精确）
    private bool _needsReexec;            // 检测到换绑（动作被游戏结束），下次请求/本帧自愈时重发命令
    private double _lastExecTime;         // 上次执行命令时刻（秒），自愈重发最小间隔用
    private float _lastWrittenTime = -1f; // 上次成功写入的 LocalTime
    private double _lastProbe;            // 上次低频绑定安全检查时刻
    private double _lastLog;              // 日志限流

    // 拖动流分离：前端拖动每 50-70ms 一发 seek，若每个中间命令都全量执行（快进释放+执行），
    // 一秒十几个动作互相打断 → 排队风暴+动画错乱（回拖"动作丢失/错误"主因）。
    // 拖动流中只记最新目标，流停 150ms（或松手/在同一 clip 停留 0.4s）后统一执行一次。
    private double _lastRequestTime;      // 上次预览请求时刻
    private string? _deferredCommand;     // 拖动流中未执行的最新命令（null=延迟的"停止"——空隙位置）
    private float _deferredTime;
    private bool _hasDeferred;
    private double _deferredSince;        // 当前延迟目标首次记下时刻（同目标停留过久=用户驻留刮擦，提前结算）

    // 延迟测时长任务：预览/定格挂载后读取绑定动画真实时长，供前端展示正确 clip 时长
    private readonly List<(string Cmd, double Due)> _pendingMeasures = new();

    /// <summary>已实测的动画时长（命令 → 秒）。预览/定格/播放时自动累积，前端用于显示与校正 clip 时长。</summary>
    public static ConcurrentDictionary<string, float> MeasuredDurations { get; } = new();

    // H1：持续移动检测锚点（1 秒窗口内位移超阈值 = 玩家在走路）
    private System.Numerics.Vector3 _anchorPos;
    private double _anchorTime;
    private bool _hasAnchor;

    // H2：本地玩家地址跟踪（切图/传送/重登时对象销毁重建）
    private nint _lastLocalAddress;

    // P1 修复：float 存 epoch 秒在 ~1.75e9 量级下 ULP≈128ms，短时比较完全失真；
    // 改用 TickCount64 单调时钟换算 double 秒，精度足够
    private double Now() => Environment.TickCount64 / 1000.0;

    public bool IsPreviewMode => _previewMode;

    public AnimationPoseFreezer(IPluginLog log, IObjectTable objectTable, IFramework framework,
        GameCommandExecutor executor, IDataManager dataManager)
    {
        _log = log;
        _objectTable = objectTable;
        _framework = framework;
        _executor = executor;
        _dataManager = dataManager;
        _framework.Update += OnFrameworkUpdate;
    }

    private bool DirectPending => _awaitTimelineIds.Length > 0;

    /// <summary>游戏当前表情是否属于我们请求的命令（族匹配：游戏实际可能执行任意变体行）。</summary>
    private bool AwaitingEmote()
    {
        if (_awaitEmoteFamily.Length == 0) return false;
        return Array.IndexOf(_awaitEmoteFamily, (ushort)CurrentEmoteId()) >= 0;
    }

    /// <summary>id 是否属于该命令的期望时间轴（Emote 表集合 ∪ 运行时学习集合）。</summary>
    private bool Awaiting(string? command, ushort timelineId)
    {
        if (timelineId == 0 || string.IsNullOrEmpty(command)) return false;
        if (Array.IndexOf(_awaitTimelineIds, timelineId) >= 0) return true;
        return LearnedTimelines.TryGetValue(command, out var learned) && learned.Contains(timelineId);
    }

    private sealed class AggEmote
    {
        public readonly List<ushort> Rows = new();
        public readonly List<ushort> Tls = new();
        public bool Loop;
        public bool Facial;
    }

    // ---- 命令 → 表情行ID + 全部时间轴行ID（首次使用时从 Emote 表构建，站立变体=同命令最小行号）----
    private void EnsureEmoteMap()
    {
        if (_emoteMap != null) return;
        var map = new ConcurrentDictionary<string, EmoteIds>();
        try
        {
            var sheet = _dataManager.GetExcelSheet<Emote>();
            if (sheet == null) { _log.Warning("Emote sheet is null"); }
            else
            {
                var rows = 0; var withCmd = 0;
                // 聚合同 TextCommand 的全部表情行：行号族（游戏实际执行任意变体行）+ 时间轴并集
                // （变体行的 ActionTimeline 含各变体实际时间轴 —— 只取最小行会漏掉如 breakdance
                // 的 7406/7407，导致表内验证永不通过、EmoteId 确认也对不上变体行号）
                // 可变类（不用元组：值类型局部副本会把先设置的 Facial 覆盖回去）
                var agg = new Dictionary<string, AggEmote>();
                foreach (var e in sheet)
                {
                    rows++;
                    try
                    {
                        if (!e.TextCommand.IsValid) continue;
                        var cmd = e.TextCommand.Value.Command.ToString();
                        if (string.IsNullOrEmpty(cmd)) continue;
                        withCmd++;
                        if (!agg.TryGetValue(cmd, out var g))
                        {
                            g = new AggEmote();
                            agg[cmd] = g;
                        }
                        if (!g.Rows.Contains((ushort)e.RowId)) g.Rows.Add((ushort)e.RowId);
                        // 表情分类：动画在面部骨架、不绑主槽0 —— 定格流程对其无效且有害
                        try
                        {
                            if (e.EmoteCategory.IsValid && e.EmoteCategory.Value.Name.ToString() == "\u8868\u60C5")
                                g.Facial = true;
                        }
                        catch { }
                        // ActionTimeline 只有 6 列（0-5），索引 6+ 会越界抛异常
                        for (var i = 0; i < 6; i++)
                        {
                            var tl = e.ActionTimeline[i];
                            if (!tl.IsValid) continue;
                            var key = tl.Value.Key.ToString();
                            if (string.IsNullOrEmpty(key)) continue;
                            var id = (ushort)tl.RowId;
                            if (!g.Tls.Contains(id)) g.Tls.Add(id);
                            if (tl.Value.IsLoop) g.Loop = true;
                        }
                    }
                    catch { }
                }
                foreach (var kv in agg)
                    map[kv.Key] = new EmoteIds(kv.Value.Rows[0], kv.Value.Tls.ToArray(), kv.Value.Loop, kv.Value.Rows.ToArray(), kv.Value.Facial);
                var facialCmds = 0; foreach (var kv in agg) if (kv.Value.Facial) facialCmds++;
                _log.Information("Emote sheet scan: rows={rows} withCmd={withCmd} cmds={cmds} facial={facialCmds}", rows, withCmd, agg.Count, facialCmds);
            }
        }
        catch (Exception ex)
        {
            _log.Error(ex, "Build emote map failed");
        }
        _emoteMap = map;
        // 表内归属反向索引（跨命令学习污染防护）
        var owners = new System.Collections.Concurrent.ConcurrentDictionary<ushort, HashSet<string>>();
        foreach (var kv in map)
            foreach (var tl in kv.Value.Timelines)
            {
                var set = owners.GetOrAdd(tl, _ => new HashSet<string>());
                lock (set) set.Add(kv.Key);
            }
        TimelineOwners = owners;
        // 预热待机集合：此时通常无表情在播（map 在首次定格请求时构建，previewMode 尚未开启），
        // 槽0上的值即主待机时间轴 —— 没有它，stance reset（循环姿态解除）永远不生效
        try
        {
            if (!IsEmoting())
            {
                var s0 = CurrentSlot0Timeline();
                if (s0 != 0 && _idleTimelines.Add(s0))
                    _log.Information("Idle timeline pre-seeded: {id}", s0);
            }
        }
        catch { }
        _log.Information("Emote map built: {n} commands", map.Count);
    }

    private bool TryResolveEmote(string command, out EmoteIds ids)
    {
        ids = default;
        if (string.IsNullOrEmpty(command)) return false;
        EnsureEmoteMap();
        if (_emoteMap == null) return false;
        if (!_emoteMap.TryGetValue(command, out ids)) return false;
        return ids.Emote != 0 && ids.Timelines != null && ids.Timelines.Length > 0;
    }

    // ---- 直接表情通道原生调用（游戏线程）----
    private bool TryGetLocalCharacter(out Character* chara)
    {
        chara = null;
        try
        {
            var local = _objectTable[0];
            if (local == null) return false;
            chara = (Character*)local.Address;
            return true;
        }
        catch { return false; }
    }

    /// <summary>
    /// 直接执行表情（游戏表情面板/系统同款原生通道）：即时、无聊天节流、表情状态机注册。
    /// 先走 ResolveTargetedEmoteId 变体解析（聊天命令在游戏内部也这么做 —— 玩家不可直接
    /// 执行表情基础行，需解析成实际变体行，如 breakdance 需解析后才生效）。
    /// DisableLogMessage=true：不刷聊天记录（等效 motion）。
    /// </summary>
    private void ExecuteEmoteDirect(ushort emoteId)
    {
        try
        {
            FFXIVClientStructs.FFXIV.Client.Game.Control.EmoteController.PlayEmoteOption opt = default;
            opt.DisableLogMessage = true;
            ushort resolved = emoteId;
            if (TryGetLocalCharacter(out var chara))
            {
                var r = chara->ResolveTargetedEmoteId(emoteId, null);
                if (r != 0) resolved = r;
            }
            FFXIVClientStructs.FFXIV.Client.Game.Control.EmoteManager.Instance()->ExecuteEmote(resolved, &opt);
        }
        catch (Exception ex)
        {
            _log.Error(ex, "ExecuteEmote failed (id={id})", emoteId);
        }
    }

    /// <summary>读取槽0当前播放的时间轴 id（确定性挂载验证）。</summary>
    private ushort CurrentSlot0Timeline()
    {
        if (!TryGetLocalCharacter(out var chara)) return 0;
        try { return chara->Timeline.TimelineSequencer.GetSlotTimeline(0); }
        catch { return 0; }
    }

    /// <summary>表情状态机当前播放的表情行ID（0=无）—— 残留场景确认"槽上就是目标动画"。</summary>
    private uint CurrentEmoteId()
    {
        if (!TryGetLocalCharacter(out var chara)) return 0;
        try { return chara->EmoteController.EmoteId; }
        catch { return 0; }
    }

    /// <summary>表情状态机是否确认正在播表情（EmoteId != 0）—— 学习变体 id 时排除中间态。</summary>
    private bool IsEmoting()
    {
        if (!TryGetLocalCharacter(out var chara)) return false;
        try { return chara->EmoteController.IsEmoting(); }
        catch { return false; }
    }

    /// <summary>
    /// 三层停表第 1、2 层：OverallSpeed（Brio 同款：游戏把整体速度应用到所有槽+粒子）
    /// + Sequencer.SetSlotSpeed（PlayActionTimeline 强制的动画走 Sequencer 速度管道，
    /// hka 控制器的 PlaybackSpeed 写入会被它覆盖 —— 必须用游戏自己的槽速度函数）
    /// + 主骨架全部控制槽 PlaybackSpeed。
    /// speed=1 恢复。
    /// </summary>
    private void SetAllControlSpeeds(float speed)
    {
        try
        {
            if (TryGetLocalCharacter(out var chara))
            {
                chara->Timeline.OverallSpeed = speed;
                // 全部 14 个槽（SetSlotSpeed 内部有 slot<14 校验）：0=动作主槽，其余含待机/表情
                for (uint slot = 0; slot < 14; slot++)
                    chara->Timeline.TimelineSequencer.SetSlotSpeed(slot, speed);
            }
        }
        catch (Exception ex) { _log.Error(ex, "SetAllControlSpeeds: sequencer failed"); }

        try
        {
            var local = _objectTable[0];
            if (local == null) return;
            var character = (Character*)local.Address;
            if (character->DrawObject == null) return;
            if (character->DrawObject->GetObjectType() != ObjectType.CharacterBase) return;
            var cb = (CharacterBase*)character->DrawObject;
            if (cb->GetModelType() != CharacterBase.ModelType.Human) return;
            var human = (Human*)character->DrawObject;
            var skeleton = human->Skeleton;
            if (skeleton == null || skeleton->PartialSkeletonCount < 1) return;
            var animatedSkeleton = skeleton->PartialSkeletons[0].GetHavokAnimatedSkeleton(0);
            if (animatedSkeleton == null) return;
            var controls = animatedSkeleton->AnimationControls;
            for (var c = 0; c < controls.Length; ++c)
            {
                var ctl = controls[c].Value;
                if (ctl != null) ctl->PlaybackSpeed = speed;
            }
        }
        catch (Exception ex)
        {
            _log.Error(ex, "SetAllControlSpeeds failed");
        }
    }

    /// <summary>
    /// 请求定格预览：执行动作命令（命令变化或动作已被游戏结束时），并把动画时间拨到 targetTime 保持。
    /// 表情命令走直接表情通道；/ac 技能等无法映射的命令走聊天通道。
    /// 拖动流（请求间隔 &lt;150ms）中的命令变化不立即执行 —— 只记最新目标，
    /// 流停后由 OnFrameworkUpdate 统一执行（防止一秒十几个动作互相打断）。
    /// M4：状态变更委托到游戏线程执行，避免 HTTP 线程与游戏线程并发读写。
    /// </summary>
    public void RequestFreezePreview(string command, float targetTime)
    {
        _framework.RunOnFrameworkThread(() => FreezeRequestCore(command, targetTime));
    }

    /// <summary>
    /// 拖动流中的"停止预览"（落在空隙）：立即恢复速度会让旧动画在拖动中乱播，
    /// 与命令一样延迟到结算时再停。非拖动状态立即停。
    /// </summary>
    public void RequestStopPreview()
    {
        _framework.RunOnFrameworkThread(() =>
        {
            if (!_previewMode && !_hasDeferred) return;
            var now = Now();
            if (now - _lastRequestTime < 0.15)
            {
                _deferredCommand = null; // null = 延迟的停止
                _hasDeferred = true;
                _deferredSince = now;
                _lastRequestTime = now;
                return;
            }
            StopPreview();
        });
    }

    private void FreezeRequestCore(string command, float targetTime, bool force = false)
    {
        var now = Now();
        var rapid = !force && now - _lastRequestTime < 0.15; // 拖动流中（不依赖 preview 状态：空隙位置会 StopPreview 打断链）
        _lastRequestTime = now;

        if (rapid && (_lastCommand != command || _needsReexec))
        {
            // 拖动流中的命令变化：记最新目标，等流停/驻留。同一命令（clip 内拖动）不延迟 —— 实时拨时间
            if (!_hasDeferred || _deferredCommand != command) _deferredSince = now;
            _deferredCommand = command;
            _deferredTime = Math.Max(0, targetTime);
            _hasDeferred = true;
            return;
        }
        _hasDeferred = false;

        // 命令变化、或动作已被游戏结束（换绑回待机）才重新执行；
        // 同一动作连续拖动只拨时间、不重播也不重置挂载等待
        if (_lastCommand != command || _needsReexec)
        {
            SetAllControlSpeeds(1f); // 恢复全部槽速度，让新动作能正常绑定起播
            // 释放旧 emote 状态机：三层停表把旧动画钉得太彻底时，游戏的表情状态机
            // 在等旧动画"播完"才接受新表情（ExecuteEmote 和聊天命令都会被拒 ——
            // slot0 卡在旧绑定、重试 8 次也不换）。把旧动画 LocalTime 快进到末尾，
            // 游戏下一帧即判定播完、结束旧 emote，新表情畅通
            var preFast = AccessMainControl(0, false);
            if (preFast.Ok && preFast.Duration > 0.05f)
                AccessMainControl(preFast.Duration, true);
            // 清表情状态标记：游戏按自身计时决定何时接受下一个表情（快进动画骗不过它，
            // 切换后仍要等满原表情时长的"忙窗口"）。EmoteId=0 是游戏 EndEmote 的状态终点，
            // 提前写 0 → 表情系统立即空闲，新表情马上可执行
            ClearEmoteId();
            // 上个是循环姿态型动作（坐地/躺椅等，快进推不到尾、快进释放无效）→ 强制主待机解除，
            // 否则游戏要求起立（1-2s），期间所有站姿命令被拒 = "很多动作出错"的根源。
            // 对已自然结束的舞蹈（slot0 已回待机）此操作幂等无害。
            if (_lastWasLoop && _idleTimelines.Count > 0 && TryGetLocalCharacter(out var stc))
            {
                try
                {
                    foreach (var idleId in _idleTimelines) { stc->Timeline.PlayActionTimeline(idleId); break; }
                    _log.Information("Freeze: stance reset before new command (previous was loop-stance)");
                }
                catch { }
            }
            _lastWasLoop = false;
            _executor.Clear(); // 丢弃还没执行的旧聊天命令，防止旧动作插队
            _directAttempts = 0;
            _chatRetries = 0;
            _learnCandidate = 0;
            _learnCandidateFrames = 0;
            _residualCandidate = 0;
            _residualCandidateFrames = 0;
            _playIdx = 0;
            _facialOnly = false;
            _gaveUp = false;
            var direct = TryResolveEmote(command, out var ids);
            if (direct)
            {
                _awaitTimelineIds = ids.Timelines;
                _awaitEmoteId = ids.Emote;
                _awaitEmoteFamily = ids.EmoteFamily;
                _awaitIsLoop = ids.AnyLoop;
                // 执行通道阶梯（全部保证正确变体）：
                // 1) 学习过的 id → 直接强制（游戏自己绑定过的变体，瞬时且正确）
                // 2) ExecuteEmote → 游戏按种族/性别/职业解析正确变体（绝大多数 1-3 帧）
                // 3) motion 变体命令 → 同样由游戏解析（~2s，顽固表情首次）
                // 绝不直接播表内原始 id —— 特殊类表情族里有其他种族/性别的变体行，
                // 播错变体会通过家族集合验证（id 在集合内）但视觉上是错误动作
                _playedTimelineId = 0;
                _facialOnly = ids.IsFacial; // 表情分类：免定格流程（执行后即完成）
                _lastWasLoop = ids.AnyLoop && !_facialOnly; // 循环姿态型：切换时需强制解除（记录给下次切换用）
                var hasLearned = LearnedTimelines.TryGetValue(command, out var lrn) && lrn.Count > 0;
                if (_facialOnly)
                {
                    _execChannel = "facial";
                    ExecuteEmoteDirect(ids.Emote);
                }
                else if (hasLearned)
                {
                    TryPlayTimelinePreferred(command);
                    _execChannel = "learned";
                }
                else if (MotionPreferred.TryGetValue(command, out var mp) && mp)
                {
                    ExecuteMotionFallback();
                    _execChannel = "motion";
                }
                else
                {
                    ExecuteEmoteDirect(ids.Emote);
                    _execChannel = "emote";
                }
            }
            else
            {
                _awaitTimelineIds = Array.Empty<ushort>();
                _awaitEmoteId = 0;
                _awaitIsLoop = false;
                _executor.ExecuteCommand(command);
            }
            _lastCommand = command;
            _lastExecTime = Now();
            _execStartedAt = Now();
            _needsReexec = false;
            _attached = false; // 等新动画挂载
            var pre = AccessMainControl(0, false);
            _preExecDuration = pre.Duration;
            _preExecBinding = pre.Binding;
            _preExecSlot0 = CurrentSlot0Timeline();
            _attachDuration = -1f;
            _lastWrittenTime = -1f;
            // 时长缓存不取挂载瞬间读数（过渡期不准，如 /bow 起播瞬间读到 3.00 而非 3.57），
            // 统一延迟 0.8s 绑定稳定后由 ProcessPendingMeasures 测量
            if (direct && _pendingMeasures.Count < 16)
                _pendingMeasures.Add((command, Now() + 0.8));
            _log.Information("Freeze preview({0}/{1}): {2} at t={3:F2}s", direct ? "direct" : "chat", _execChannel, command, Math.Max(0, targetTime));
        }
        _previewMode = true;
        _pendingCommand = command;
        _pendingTime = Math.Max(0, targetTime);
    }

    /// <summary>
    /// 退出定格预览模式，恢复角色自由播放。
    /// 表情由状态机管理：恢复全部槽速度后自然播放完毕回归待机，无需手动清除。
    /// </summary>
    public void StopPreview()
    {
        if (!_previewMode) return;
        _previewMode = false;
        _pendingCommand = null;
        _lastCommand = null;
        _attached = false;
        _hasDeferred = false;
        _awaitTimelineIds = Array.Empty<ushort>();
        _awaitEmoteId = 0;
        _awaitIsLoop = false;
        SetAllControlSpeeds(1f); // 恢复全部槽速度与整体速度，角色回归自由动画
        _log.Information("Freeze preview stopped");
    }

    private void OnFrameworkUpdate(IFramework framework)
    {
        // 待机时间轴观察（学习排除集合）—— 预览未激活时低频采样
        ObserveIdleTimeline();

        // H2：切图/重登检测 —— 本地玩家对象地址变化即退出定格
        var localAddr = nint.Zero;
        try { localAddr = _objectTable[0]?.Address ?? nint.Zero; } catch { }
        if (localAddr != _lastLocalAddress)
        {
            _lastLocalAddress = localAddr;
            if (_previewMode && localAddr != nint.Zero)
            {
                _log.Warning("Local player changed (territory/relog), stopping freeze preview");
                StopPreview();
            }
        }

        // 预览测时长任务：独立于定格状态，每帧检查到期任务
        ProcessPendingMeasures();

        // 拖动流结算：150ms 无新请求（=松手/停下）统一执行最新目标。
        // 注意：不做"驻留提前结算"—— 大幅拖拽穿过长 clip（12-16s 舞蹈）耗时 >0.4s 会触发
        // 中途执行（释放旧+执行新的完整周期），来回大幅拖拽反复触发 = 连锁执行 = 叠加/吞动作。
        // clip 内刮擦反馈由同命令实时拨时间路径提供（首次执行后即实时）。
        // force 绕过流判定（结算时距上次请求必然 >150ms，保险起见仍强制）。
        if (_hasDeferred && Now() - _lastRequestTime > 0.15)
        {
            var cmd = _deferredCommand;
            var t = _deferredTime;
            _hasDeferred = false;
            if (cmd == null)
            {
                _log.Information("Freeze settled after drag: stop (gap)");
                StopPreview();
            }
            else
            {
                _log.Information("Freeze settled after drag: {cmd} at t={t:F2}s", cmd, t);
                FreezeRequestCore(cmd, t, force: true);
            }
        }

        if (!_previewMode || _pendingCommand == null) return;

        // H1：定格持续保持，玩家持续移动时解除。
        // 锚点式判断：1 秒内位移超过 1.5m 才算玩家在走路（走路 ~2m/s 必触发）；
        // 动作自带的根运动位移是一次性的、服务器位置修正是毫米级 —— 都不会误触发
        try
        {
            var local = _objectTable[0];
            var pos = local?.Position ?? System.Numerics.Vector3.Zero;
            var now = Now();
            if (!_hasAnchor || now - _anchorTime > 1.0)
            {
                _anchorPos = pos;
                _anchorTime = now;
                _hasAnchor = true;
            }
            else if ((pos - _anchorPos).LengthSquared() > 2.25f) // 1.5m²
            {
                _log.Information("Player moving sustained, releasing freeze preview");
                StopPreview();
                return;
            }
        }
        catch { }

        if (!_attached)
        {
            AttachPhase();
            return;
        }

        // 面部/免钉定类：动画不在主槽（面部骨架/装备动作等）—— 不停表不写时间（写了会钉错
        // 别的动画 = 错误动作），让动作自然播完。若之后主槽迟到了该命令的绑定（慢绑定的身体
        // 动作），升级回正常定格
        if (_facialOnly)
        {
            var fs = CurrentSlot0Timeline();
            if (fs != 0 && !_idleTimelines.Contains(fs) && Awaiting(_pendingCommand, fs))
            {
                _facialOnly = false;
                _lastWrittenTime = -1f;
                _log.Information("Freeze no-pin upgraded to pinned (tl={id})", fs);
            }
            return;
        }

        // 停表保持（三层防御）：游戏每帧可能重算各槽速度，单一控制槽的 0 会被覆盖，
        // 被覆盖后动画偷偷推进 → "停不住"；伴随槽继续播 → "抽搐"。每帧全量压 0 + 漂移校正兜底。
        // 拖动流中目标已过时且游戏已换绑（_needsReexec）时不写时间（会写进待机控制），等结算
        if (!(_hasDeferred && _needsReexec))
        {
            SetAllControlSpeeds(0f);
            // 循环动画取模：单轮时长 1.67s 的舞蹈在 clip 内 t=4s 应显示 4%1.67≈0.66s 的循环姿态；
            // 直接钳制到单轮末尾会被游戏 wrap 重置 → 每帧漂移对抗（抽搐）
            var target = _pendingTime;
            if (_awaitIsLoop && _attachDuration > 0.05f && _pendingTime > _attachDuration)
                target = _pendingTime % _attachDuration;
            if (Math.Abs(target - _lastWrittenTime) > 0.001f)
            {
                if (AccessMainControl(target, true).Ok)
                {
                    _lastWrittenTime = target;
                    _log.Information("Freeze hold: LocalTime={time}s", target);
                }
            }
            else
            {
                // 漂移校正（第 3 层）：速度写入被游戏覆盖时，主槽 LocalTime 会偷偷前进；
                // 偏离目标 >30ms 才回写，避免无意义的每帧对抗
                var cur = AccessMainControl(0, false);
                if (cur.Ok && cur.LocalTime >= 0 && Math.Abs(cur.LocalTime - target) > 0.03f)
                {
                    if (AccessMainControl(target, true).Ok)
                    {
                        _lastWrittenTime = target;
                        if (Now() - _lastLog > 0.5)
                        {
                            _lastLog = Now();
                            _log.Information("Freeze drift-correct: {c:F2} -> {t:F2}s (speed override detected)", cur.LocalTime, target);
                        }
                    }
                }
            }
        }

        // 低频安全检查：确认绑定没被游戏换掉（意外解冻/动作被结束）
        if (Now() - _lastProbe < 0.25) return;
        _lastProbe = Now();
        var probe = AccessMainControl(0, false);
        if (!probe.Ok)
        {
            // M1：拿不到控制槽 —— 重走挂载流程，不静默放弃
            _attached = false;
            _preExecDuration = -1f;
            _lastWrittenTime = -1f;
            return;
        }
        // 直接通道：槽0时间轴 id 是动画身份（集合语义，容忍游戏把强制 id 规范化成它解析的变体）。
        // id 仍在集合内时，时长/指针波动只是过渡期读数失真 → 刷新基准，不触发重播；id 变了（回待机）→ 自愈
        var curSlot0 = CurrentSlot0Timeline();
        if (DirectPending && !_idleTimelines.Contains(curSlot0) && Awaiting(_pendingCommand, curSlot0))
        {
            _attachDuration = probe.Duration;
            _attachBinding = probe.Binding;
            return;
        }
        if ((_attachBinding != 0 && probe.Binding != _attachBinding)
            || (_attachDuration >= 0 && Math.Abs(probe.Duration - _attachDuration) > 0.05f))
        {
            // 游戏把槽换绑了（动作结束→待机/意外解冻）。
            // 自愈：恢复速度后重新播放动作重新定格；后续请求也会因此强制重发（修复"回拉无变化"）。
            // 拖动流中不自愈重播（旧目标已过时，结算会统一处理；此刻重播会和延迟目标交错=动作叠加）
            _needsReexec = true;
            if (!_hasDeferred && Now() - _lastExecTime > 0.5 && _pendingCommand != null)
            {
                SetAllControlSpeeds(1f); // 恢复全部槽速度，让重发的动作能正常起播
                _executor.Clear();
                if (_awaitEmoteId != 0)
                {
                    _directAttempts = 0;
                    // 自愈优先直接时间轴重放（零成本即时；idle 重置场景主力）
                    if (!TryPlayTimelinePreferred(_pendingCommand))
                        ExecuteEmoteDirect(_awaitEmoteId);
                }
                else
                {
                    _executor.ExecuteCommand(_pendingCommand);
                }
                _lastExecTime = Now();
                _needsReexec = false;
                _attached = false;
                _preExecDuration = probe.Duration;
                _preExecBinding = probe.Binding;
                _attachDuration = -1f;
                _lastWrittenTime = -1f;
                _log.Information("Freeze: animation ended by game, re-playing {cmd}", _pendingCommand);
            }
            return;
        }
    }

    /// <summary>
    /// 挂载等待阶段：确认"要定格的那个动画"已经绑到控制槽之后才允许写时间。
    /// 直接通道：GetSlotTimeline(0) ∈ 期望时间轴集合（表情可能有多个变体，实际绑定的
    /// 未必是 [0] 号 —— 单 id 验证会导致部分动作永不挂载="停不住"）+ 绑定指针已切换 → 挂载；
    ///           未挂上时零成本重试，绝不把时间写进未确认的动画。
    /// 聊天通道：绑定指针/时长变化 → 挂载；超时重发（≤2次），仍不行则放弃本次（不写时间）。
    /// </summary>
    /// <summary>
    /// 延迟挂起期间的观察学习：上一目标（已执行、未挂载就被拖走）的动画可能在拖动中才生效
    /// （motion 固有 ~2s 延迟）—— 状态机确认（EmoteId 族匹配）+ 非待机 + 未知 id 即学习，
    /// 不挂载（目标已过时）。学到后下次拖到该命令直接命中验证。
    /// </summary>
    private void ObserveDeferredTarget()
    {
        if (_pendingCommand == null || !DirectPending || _facialOnly) return;
        if (Now() - _lastExecTime < 0.3) return; // 命令刚发出，等生效
        var slot0 = CurrentSlot0Timeline();
        if (slot0 == 0 || _idleTimelines.Contains(slot0)) return;
        if (Awaiting(_pendingCommand, slot0)) return; // 已知
        if (!AwaitingEmote()) return; // 状态机没确认在播我们的表情
        LearnTimeline(_pendingCommand, slot0);
        var (ok, dur, _, _) = AccessMainControl(0, false);
        if (ok && dur > 0.05f && !KnownAttachDurations.TryGetValue(_pendingCommand, out _))
            KnownAttachDurations[_pendingCommand] = dur; // 变体时长基准（供时长匹配路径）
        _log.Information("Freeze learned timeline {id} for {cmd} (deferred-observed)", slot0, _pendingCommand);
    }

    private void AttachPhase()
    {
        // 拖动流中：挂载目标已过时（延迟中了新命令），停止旧目标的重试/motion 兜底 ——
        // 否则兜底命令会和结算后的新动作交错执行，表现为"两个动作叠加"。
        // 但继续观察学习：上一目标的动画可能此时才生效（motion 固有 ~2s 延迟常落在拖动中），
        // 学到变体 id 后下次直接命中（否则每轮都卡在首次学习的边缘）
        if (_hasDeferred) { ObserveDeferredTarget(); return; }
        var probe0 = AccessMainControl(0, false);
        if (!probe0.Ok) return;
        var d = probe0.Duration;
        if (_preExecDuration < 0) _preExecDuration = d;

        if (DirectPending)
        {
            var slot0 = CurrentSlot0Timeline();

            // 面部表情类（表预测）：执行后 0.3s 即完成 —— 不等主槽绑定（等不到）、不重试
            // （角色已在做正确表情）、不学习（面部 timeline 学进去会被当主槽 id 播放 = 错误动作）
            if (_facialOnly)
            {
                if (Now() - _execStartedAt > 0.3)
                {
                    _attached = true;
                    _attachDuration = -1f;
                    _log.Information("Freeze facial emote done (no pin): {cmd}", _pendingCommand);
                }
                return;
            }

            // 集合验证（v0.5.11 已验证语义）：槽0 属于该命令（表内族 ∪ 学习过）且非待机 → 挂载。
            // 不能用"精确等于播放 id"—— 游戏有时会把强制的 id 规范化成它自己解析的变体
            // （v0.5.13 教训：精确匹配误判失败 → 不停重放 = 抽搐；重放 ladder 又闪过错误变体 = 动作错）。
            // 待机排除防止把待机绑定当自己的动画钉住。
            if (slot0 != 0 && !_idleTimelines.Contains(slot0) && Awaiting(_pendingCommand, slot0))
            {
                // hka 控制槽换绑通常滞后 1-2 帧，等绑定指针切换（或 1s 短超时，游戏复用控制时）再钉时间
                if (probe0.Binding != _preExecBinding || Now() - _lastExecTime > 1.0)
                {
                    _attached = true;
                    _attachDuration = d;
                    _attachBinding = probe0.Binding;
                    LearnTimeline(_pendingCommand, slot0); // 挂载成功即记忆（集合确认过的实际变体）
                    KnownAttachDurations[_pendingCommand!] = d;
                    if (_pendingCommand != null && _directAttempts >= 2)
                        MotionPreferred[_pendingCommand] = true;
                    _log.Information("Freeze attached direct (tl={id}, dur {d:F2}s)", slot0, d);
                }
                return;
            }
            // 面部表情类确认：ExecuteEmote 已被状态机接受（EmoteId 族匹配）但主槽0 保持不变
            // （表情动画在面部骨架）→ 无主槽可定格，执行即完成。计时用 _execStartedAt（不随
            // retry 重置 —— 否则 0.3s 的 retry 不断重置计时，0.5s 判定永远达不到）。
            // 不 LearnTimeline（面部 timeline 学进去会被当主槽 id 播放 = 错误动作），不重试
            if (slot0 != 0 && slot0 == _preExecSlot0 && AwaitingEmote() && Now() - _execStartedAt > 0.45)
            {
                _attached = true;
                _facialOnly = true;
                _attachDuration = -1f;
                _log.Information("Freeze facial-only emote confirmed (no slot-0 pin): {cmd}", _pendingCommand);
                return;
            }
            // 学习路径 A（表情状态机确认）：EmoteId == 期望表情 且绑定确实换成新值且非待机 ——
            // 用于变体时间轴（/breakdance 实际绑 7407，不在 Emote 表 [0..5]）与残留场景。
            // CanLearnTimeline 排除过渡窗口的待机/残留（曾把待机 3 学进缓存 → 之后永远钉待机 = 吞动作）
            if (CanLearnTimeline(slot0) && _directAttempts >= 1 && AwaitingEmote())
            {
                LearnTimeline(_pendingCommand, slot0);
                _log.Information("Freeze learned timeline {id} for {cmd} (state-confirmed)", slot0, _pendingCommand);
                return;
            }
            // 学习路径 A2（残留确认）：EmoteId == 期望表情 且 slot0 == 执行前值（残留的就是目标 ——
            // 前一轮 motion 的产物还在播，"变化检测"全部失效的死锁场景）且稳定 ≥5 帧非待机 ——
            // 状态机明确说目标表情在播，槽上必是它的变体（过渡窗口的旧动画撑不过 5 帧稳定 +
            // 0.8s 时限，不会误学）
            if (slot0 != 0 && slot0 == _preExecSlot0 && !_idleTimelines.Contains(slot0)
                && AwaitingEmote() && Now() - _lastExecTime > 0.8)
            {
                if (slot0 == _residualCandidate) _residualCandidateFrames++;
                else { _residualCandidate = slot0; _residualCandidateFrames = 1; }
                if (_residualCandidateFrames >= 5)
                {
                    _residualCandidateFrames = 0;
                    LearnTimeline(_pendingCommand, slot0);
                    _log.Information("Freeze learned timeline {id} for {cmd} (residual-confirmed)", slot0, _pendingCommand);
                    return;
                }
            }
            else { _residualCandidate = 0; _residualCandidateFrames = 0; }
            // 学习路径 B（变化检测）：重试后槽0换成新值且非待机且表情在播
            if (CanLearnTimeline(slot0) && _directAttempts >= 3 && IsEmoting())
            {
                LearnTimeline(_pendingCommand, slot0);
                _log.Information("Freeze learned timeline {id} for {cmd} (by change)", slot0, _pendingCommand);
                return;
            }
            // 学习路径 C（motion 确认）：motion 变体命令播放的动画不设置 EmoteId（A/B 的
            // 状态机确认对它失效），其生效的直接证据是槽0 变成 ≠ motion 发出时刻快照的值 ——
            // 等待期槽0=待机且与快照相同，绝不学习（曾把待机 3 学进缓存 → 吞动作）
            if (CanLearnTimeline(slot0) && _directAttempts >= 4 && slot0 != _motionSentSlot0)
            {
                if (slot0 == _learnCandidate) _learnCandidateFrames++;
                else { _learnCandidate = slot0; _learnCandidateFrames = 1; }
                if (_learnCandidateFrames >= 3)
                {
                    _learnCandidateFrames = 0;
                    LearnTimeline(_pendingCommand, slot0);
                    _log.Information("Freeze learned timeline {id} for {cmd} (motion-confirmed)", slot0, _pendingCommand);
                    return;
                }
            }
            else { _learnCandidate = 0; _learnCandidateFrames = 0; }
            // 有界重试（防命令风暴）：0.6s 间隔，最多 2 次重试 —— 第 1 次重发 ExecuteEmote、
            // 第 2 次一条 motion。绝不播表内原始 id。**没有无限兜底** —— 曾每 0.35s 无限发
            // motion，对不绑主槽的动作每条都真执行（~2s 后落地）→ 用户看到"没写过的动作"
            if (Now() - _lastExecTime > 0.6 && _directAttempts < 2 && !_gaveUp)
            {
                _directAttempts++;
                if (_directAttempts == 1)
                {
                    _execChannel = "emote";
                    ExecuteEmoteDirect(_awaitEmoteId);
                }
                else
                {
                    _execChannel = "motion";
                    ExecuteMotionFallback();
                }
                _lastExecTime = Now();
                _log.Information("Freeze direct retry {n} via {ch} (slot0={cur})", _directAttempts, _execChannel, slot0);
            }
            else if (_directAttempts >= 2 && Now() - _execStartedAt > 3.0 && !_gaveUp)
            {
                // 有界放弃：命令已发完（初始 + 2 次重试）仍未挂载 —— 静默等待（不写时间不钉错），
                // 下次请求会因 _needsReexec 重发。游戏侧命令可能仍在途并最终播放（可接受）。
                _gaveUp = true;
                _needsReexec = true;
                _log.Information("Freeze: bounded give-up after retries, waiting quietly ({cmd})", _pendingCommand);
            }
            // 未挂载期间不写时间（绝不钉错姿势），每帧继续轻量轮询
            return;
        }

        // 聊天通道（/ac 技能等）：等命令真正执行完再判断，避免轮询到上一条命令的动作
        if (_executor.PendingCount > 0) return;
        if (probe0.Binding != _preExecBinding || Math.Abs(d - _preExecDuration) > 0.05f)
        {
            // 时长校验：绑定变化但时长与该命令历史实测差 >0.5s → 是前序动作的残留绑定
            // （在途 motion/表情命令干扰），不是我们的动画 —— 拒绝挂载继续等（防"动作错误"）
            if (_pendingCommand != null
                && MeasuredDurations.TryGetValue(_pendingCommand, out var knownDur)
                && knownDur > 0.05f && d > 0.05f && Math.Abs(d - knownDur) > 0.5f)
            {
                _log.Information("Freeze chat: binding changed but dur {d:F2}s != known {k:F2}s, waiting for real animation ({cmd})", d, knownDur, _pendingCommand);
                return;
            }
            _attached = true;
            _attachDuration = d;
            _attachBinding = probe0.Binding;
            _log.Information("Freeze attached (dur {d:F2}s)", d);
        }
        else if (Now() - _lastExecTime > 0.5)
        {
            // 超时仍未换绑：盲挂旧动画会显示错误动作。持续重发（≤6 次覆盖前序动作的忙窗口
            // —— 命令在窗口内会被游戏吞掉，2 次就放弃会偶发"技能动作没反应"），仍不行才放弃。
            if (_pendingCommand != null && _chatRetries < 6)
            {
                _chatRetries++;
                _executor.Clear();
                _executor.ExecuteCommand(_pendingCommand);
                _lastExecTime = Now();
                _log.Information("Freeze chat re-exec #{n} ({cmd})", _chatRetries, _pendingCommand);
            }
            else if (_chatRetries == 6)
            {
                _chatRetries = 7; // 只记一次
                _needsReexec = true; // 后续请求强制重发；本次保持未挂载，不写时间
                _log.Warning("Freeze: chat command did not rebind animation, giving up this request ({cmd})", _pendingCommand);
            }
        }
    }

    /// <summary>
    /// 延迟测量动画时长：命令执行 0.6s 后（动画已挂载）读取绑定动画真实时长存入 MeasuredDurations。
    /// 供 /preview 用 —— 预览一个动作即可得到它的真实时长，前端据此显示/校正 clip 时长。
    /// </summary>
    public void MeasureDurationDelayed(string command)
    {
        if (string.IsNullOrEmpty(command)) return;
        _framework.RunOnFrameworkThread(() =>
        {
            if (_pendingMeasures.Count < 16) // 防积压上限
                _pendingMeasures.Add((command, Now() + 0.6));
        });
    }

    /// <summary>清表情状态标记（EmoteId=0 = 游戏 EndEmote 的状态终点）—— 消除切换后的"忙窗口"。</summary>
    private void ClearEmoteId()
    {
        if (!TryGetLocalCharacter(out var chara)) return;
        try { chara->EmoteController.EmoteId = 0; }
        catch (Exception ex) { _log.Error(ex, "ClearEmoteId failed"); }
    }

    /// <summary>motion 变体兜底：/xxx motion 不进表情状态机、无忙窗口（状态机被去重/阻塞时走它）。</summary>
    private void ExecuteMotionFallback()
    {
        if (string.IsNullOrEmpty(_pendingCommand)) return;
        // 记录发出时刻槽0快照：生效证据=槽0变成≠快照的值（等待期槽0=待机且==快照，不是 motion 产物）
        var cur = CurrentSlot0Timeline();
        if (cur != 0) _motionSentSlot0 = cur;
        _executor.ExecuteCommand(_pendingCommand.Trim() + " motion");
    }

    /// <summary>学习前置校验：非空、确实换过绑定（≠执行前值）、不是待机 —— 防止学到过渡窗口的待机/残留。</summary>
    private bool CanLearnTimeline(ushort slot0)
        => slot0 != 0 && slot0 != _preExecSlot0 && !_idleTimelines.Contains(slot0);

    /// <summary>低频观察待机时间轴（预览未激活且无表情时槽0上的值）—— 用于学习排除。</summary>
    private void ObserveIdleTimeline()
    {
        if (Now() - _lastIdleObserve < 0.5) return;
        _lastIdleObserve = Now();
        if (_previewMode || _hasDeferred || IsEmoting()) return;
        var slot0 = CurrentSlot0Timeline();
        if (slot0 == 0 || _idleTimelines.Contains(slot0)) return;
        _idleTimelines.Add(slot0);
        _log.Information("Idle timeline observed: {id} (excluded from learning)", slot0);
    }

    // 时间轴 → 拥有它的命令集合（表内权威归属）：跨命令学习污染防护 —— 压测实测 /mandervilledance
    // 被学进 /tremble 的 3771（5 个命令共学同一 id），播放污染 id = 直接播出别人的动画 = "不生效"
    private static System.Collections.Concurrent.ConcurrentDictionary<ushort, HashSet<string>>? TimelineOwners;

    /// <summary>表内归属校验：id 在表内归属其他命令（且不归属本命令）→ 绝不学习/播放。</summary>
    private static bool OwnerAllows(string? command, ushort timelineId)
    {
        if (string.IsNullOrEmpty(command) || TimelineOwners == null) return true;
        if (!TimelineOwners.TryGetValue(timelineId, out var owners)) return true; // 表外 id（真正的变体）不受限
        return owners.Contains(command);
    }

    private static void LearnTimeline(string? command, ushort timelineId)
    {
        if (string.IsNullOrEmpty(command) || timelineId == 0) return;
        if (!OwnerAllows(command, timelineId))
        {
            // 表内归属别的命令 —— 拒学（跨命令污染是"特殊动作不生效/错误"的根源之一）
            return;
        }
        var list = LearnedTimelines.GetOrAdd(command, _ => new List<ushort>());
        lock (list) { if (!list.Contains(timelineId)) list.Add(timelineId); } // 有序：最近学习的在重试轮换中优先
    }

    /// <summary>延迟测量前的身份校验：延迟期间用户可能已拖到别的动作，防止把别人的时长记串（v0.5.6 修复）。</summary>
    private bool VerifyMeasureTarget(string cmd)
    {
        try
        {
            // 已拖到别的动作：丢弃过期测量
            if (_previewMode && _pendingCommand != null && _pendingCommand != cmd) return false;
            // 可校验的（表情命令）：槽0 仍须是该命令的时间轴（表内或学习集合），且不是待机
            if (_emoteMap != null && _emoteMap.TryGetValue(cmd, out var ids))
            {
                var slot0 = CurrentSlot0Timeline();
                if (slot0 != 0
                    && !_idleTimelines.Contains(slot0)
                    && Array.IndexOf(ids.Timelines, slot0) < 0
                    && !(LearnedTimelines.TryGetValue(cmd, out var learned) && learned.Contains(slot0)))
                    return false;
            }
            return true;
        }
        catch { return true; }
    }

    private void ProcessPendingMeasures()
    {
        for (var i = _pendingMeasures.Count - 1; i >= 0; i--)
        {
            if (Now() < _pendingMeasures[i].Due) continue;
            var cmd = _pendingMeasures[i].Cmd;
            _pendingMeasures.RemoveAt(i);
            var (ok, dur, _, _) = AccessMainControl(0, false);
            if (ok && dur > 0.05f && VerifyMeasureTarget(cmd))
            {
                MeasuredDurations[cmd] = dur;
                _log.Information("Measured duration: {cmd} = {dur:F2}s", cmd, dur);
            }
        }
    }

    /// <summary>
    /// 访问主控制槽（SimpleHeels 同款路径：PartialSkeletons[0]->GetHavokAnimatedSkeleton(0)->AnimationControls[0]）。
    /// write=false 只读绑定动画真实时长与当前 LocalTime；write=true 写入 LocalTime（钳制在真实时长内）。
    /// 只读写主槽：把动作的目标时间写进其他槽会让它们跳帧（抽搐）；速度冻结走 SetAllControlSpeeds。
    /// </summary>
    private (bool Ok, float Duration, long Binding, float LocalTime) AccessMainControl(float time, bool write)
    {
        try
        {
            var local = _objectTable[0];
            if (local == null) return (false, -1, 0, -1);
            var character = (Character*)local.Address;
            if (character->DrawObject == null) return (false, -1, 0, -1);
            if (character->DrawObject->GetObjectType() != ObjectType.CharacterBase) return (false, -1, 0, -1);
            var cb = (CharacterBase*)character->DrawObject;
            if (cb->GetModelType() != CharacterBase.ModelType.Human) return (false, -1, 0, -1);
            var human = (Human*)character->DrawObject;

            var skeleton = human->Skeleton;
            if (skeleton == null) return (false, -1, 0, -1);
            for (var i = 0; i < skeleton->PartialSkeletonCount && i < 1; ++i)
            {
                var partialSkeleton = &skeleton->PartialSkeletons[i];
                var animatedSkeleton = partialSkeleton->GetHavokAnimatedSkeleton(0);
                if (animatedSkeleton == null) continue;

                var controls = animatedSkeleton->AnimationControls;
                if (controls.Length == 0) continue;
                var control = controls[0].Value;
                if (control == null)
                {
                    // 槽 0 为空时兜底找第一个非空槽（动画可能还没完全挂载）
                    for (var c = 1; c < controls.Length; ++c)
                    {
                        if (controls[c].Value != null) { control = controls[c].Value; break; }
                    }
                }
                if (control == null) continue;

                var duration = -1f;
                long binding = 0;
                if (control->Binding.ptr != null)
                {
                    binding = (long)control->Binding.ptr;
                    if (control->Binding.ptr->Animation.ptr != null)
                        duration = control->Binding.ptr->Animation.ptr->Duration;
                }

                if (write)
                {
                    // 钳制：写入超过动画真实时长会被游戏判定"播完"→ 结束动作回待机
                    var t = time;
                    if (duration > 0.05f) t = Math.Min(t, duration);
                    control->hkaAnimationControl.LocalTime = t;
                }
                return (true, duration, binding, control->hkaAnimationControl.LocalTime);
            }
        }
        catch (Exception ex)
        {
            _log.Error(ex, "AccessMainControl failed");
        }
        return (false, -1, 0, -1);
    }

    /// <summary>
    /// 解除姿态锁定：坐地/躺椅等持续姿态（EmoteLoop 模式）会拒绝后续站姿命令（游戏要起立，
    /// 1-2s）—— 坐地后所有普通动作全部"迟到/失败"的根源。直接强制主待机时间轴立即解除。
    /// </summary>
    private void BreakStanceLock()
    {
        try
        {
            if (!TryGetLocalCharacter(out var chara)) return;
            if (!chara->EmoteController.IsInEmoteLoop()) return;
            foreach (var id in _idleTimelines)
            {
                chara->Timeline.PlayActionTimeline(id);
                _log.Information("Freeze: broke stance lock via idle timeline {id}", id);
                return;
            }
        }
        catch (Exception ex) { _log.Error(ex, "BreakStanceLock failed"); }
    }

    /// <summary>直接强制时间轴：候选只取学习缓存 —— 游戏自己绑定过的 id（种族/性别/职业正确变体）。
    /// 绝不播表内原始 id（特殊类表情族含其他种族/性别的变体行，播错会通过集合验证但视觉错误）。
    /// </summary>
    private bool TryPlayTimelinePreferred(string command)
    {
        if (!LearnedTimelines.TryGetValue(command, out var learned) || learned.Count == 0) return false;
        // 只播归属校验通过的 learned id（污染条目直接跳过 —— 它们是别的命令的动画）
        List<ushort> cands;
        lock (learned) cands = learned.Where(id => OwnerAllows(command, id)).ToList();
        if (cands.Count == 0) return false;
        var playId = cands[_playIdx % cands.Count];
        if (!TryGetLocalCharacter(out var chara)) return false;
        try
        {
            chara->Timeline.PlayActionTimeline(playId);
            _playedTimelineId = playId;
            return true;
        }
        catch (Exception ex)
        {
            _log.Error(ex, "PlayActionTimeline failed (id={id})", playId);
            return false;
        }
    }

    /// <summary>调试端点数据：槽0时间轴/表情状态/绑定时长（诊断动画通道行为）。</summary>
    public string GetDebugAnimState()
    {
        try
        {
            var (ok, dur, binding, lt) = AccessMainControl(0, false);
            var state = new
            {
                slot0 = CurrentSlot0Timeline(),
                emoteId = CurrentEmoteId(),
                isEmoting = IsEmoting(),
                controlOk = ok,
                duration = Math.Round(dur, 2),
                localTime = Math.Round(lt, 2),
                binding = binding,
                previewMode = _previewMode,
                pendingCommand = _pendingCommand,
                attached = _attached,
                idleTimelines = _idleTimelines.ToArray(),
                learned = LearnedTimelines.ToDictionary(kv => kv.Key, kv => kv.Value.ToArray()),
                motionPreferred = MotionPreferred.ToArray(),
                knownDurations = KnownAttachDurations.ToArray()
            };
            return System.Text.Json.JsonSerializer.Serialize(state);
        }
        catch (Exception ex)
        {
            return "{\"error\":\"" + ex.Message.Replace("\"", "'") + "\"}";
        }
    }

    public void Dispose()
    {
        StopPreview();
        _framework.Update -= OnFrameworkUpdate;
    }
}
