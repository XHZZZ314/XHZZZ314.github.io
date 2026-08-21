using System;
using System.Collections.Generic;
using System.IO;
using System.Net;
using System.Net.Http;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using System.Threading;
using System.Threading.Tasks;
using Dalamud.Plugin.Services;
using Lumina.Excel;
using Lumina.Excel.Sheets;
using Action = Lumina.Excel.Sheets.Action;

namespace ChoreoHelper;

public sealed class HttpServer : IDisposable
{
    private readonly IDataManager _dataManager;
    private readonly IPluginLog _log;
    private readonly ActionPreviewer? _previewer;
    private readonly PlaybackManager? _playback;
    private readonly AnimationPoseFreezer? _freezer;
    private HttpListener? _listener;
    private CancellationTokenSource? _cts;
    private Task? _serverTask;
    private const int Port = 48794;

    private static readonly HttpClient _httpClient = new HttpClient
    {
        Timeout = TimeSpan.FromSeconds(10)
    };

    private static readonly string[] CorsHeaders =
    [
        "Access-Control-Allow-Origin: *",
        "Access-Control-Allow-Methods: GET, POST, OPTIONS",
        "Access-Control-Allow-Headers: Content-Type",
        // Chrome 137+ 强制 Private Network Access 预检：公网页面调 localhost 缺此头会被静默拦截
        "Access-Control-Allow-Private-Network: true"
    ];

    // 播放状态串行化：快速连点 Play/Seek/Stop 时防止交错执行
    private readonly SemaphoreSlim _playbackGate = new(1, 1);

    public HttpServer(IDataManager dataManager, IPluginLog log, ActionPreviewer? previewer = null, PlaybackManager? playback = null, AnimationPoseFreezer? freezer = null)
    {
        _dataManager = dataManager;
        _log = log;
        _previewer = previewer;
        _playback = playback;
        _freezer = freezer;
    }

    public void Start()
    {
        try
        {
            _listener = new HttpListener();
            _listener.Prefixes.Add($"http://localhost:{Port}/");
            _listener.Start();
            _cts = new CancellationTokenSource();
            _serverTask = Task.Run(() => ListenLoop(_cts.Token));
            _log.Information("HTTP server listening on http://localhost:{port}/", Port);
        }
        catch (Exception ex)
        {
            _log.Error(ex, "Failed to bind HTTP port {port} (可能被占用)", Port);
            try { _listener?.Close(); } catch { }
            _listener = null;
        }
    }

    private async Task ListenLoop(CancellationToken ct)
    {
        while (!ct.IsCancellationRequested && _listener!.IsListening)
        {
            HttpListenerContext ctx;
            try { ctx = await _listener.GetContextAsync(); }
            catch (HttpListenerException) { break; }
            _ = Task.Run(async () => await HandleRequest(ctx, ct), ct);
        }
    }

    private async Task HandleRequest(HttpListenerContext ctx, CancellationToken ct)
    {
        try
        {
            var path = ctx.Request.Url?.AbsolutePath ?? "/";
            var query = System.Web.HttpUtility.ParseQueryString(ctx.Request.Url?.Query ?? "");
            var method = ctx.Request.HttpMethod;

            if (method == "OPTIONS")
            {
                ctx.Response.StatusCode = 204;
                AddCorsHeaders(ctx.Response);
                ctx.Response.Close();
                return;
            }

            if (method == "POST")
            {
                string postJson;
                if (path == "/preview") { HandlePreview(ctx); return; }
                if (path == "/playback/start" || path == "/playback/seek" || path == "/playback/freeze")
                {
                    // 播放状态变更串行化：防止并发请求交错执行导致时间轴错乱
                    await _playbackGate.WaitAsync();
                    try
                    {
                        if (path == "/playback/start") postJson = HandlePlaybackStart(ctx);
                        else if (path == "/playback/seek") postJson = HandlePlaybackSeek(ctx);
                        else postJson = HandlePlaybackFreeze(ctx);
                    }
                    finally { _playbackGate.Release(); }
                }
                else if (path == "/playback/stop")
                {
                    await _playbackGate.WaitAsync();
                    try { postJson = HandlePlaybackStop(); }
                    finally { _playbackGate.Release(); }
                }
                else { AddCorsHeaders(ctx.Response); ctx.Response.StatusCode = 404; ctx.Response.Close(); return; }
                ctx.Response.ContentType = "application/json; charset=utf-8";
                AddCorsHeaders(ctx.Response);
                var postBytes = System.Text.Encoding.UTF8.GetBytes(postJson);
                ctx.Response.OutputStream.Write(postBytes, 0, postBytes.Length);
                ctx.Response.Close();
                return;
            }

            ctx.Response.ContentType = "application/json; charset=utf-8";
            AddCorsHeaders(ctx.Response);

            string? json;

            // Async endpoints (lyrics via NetEase Music API)
            if (method == "GET" && path == "/lyrics/search")
            {
                json = await SearchLyrics(query["s"] ?? "");
            }
            else if (method == "GET" && path == "/lyrics")
            {
                json = await GetLyrics(query["id"], query["url"]);
            }
            else
            {
                json = path switch
                {
                    "/health" => "{\"status\":\"ok\"}",
                    "/actions" => GetActionsJson(query["id"]),
                    "/actions/emotes" => GetEmotesJson(),
                    "/actions/emote-durations" => GetEmoteDurationsJson(),
                    "/actions/measured-durations" => GetMeasuredDurationsJson(),
                    "/debug/animstate" => _freezer?.GetDebugAnimState() ?? "{\"error\":\"no freezer\"}",
                    "/actions/races" => GetRacesJson(),
                    "/dancers" => GetDancersJson(),
                    "/classjobs" => GetClassJobsJson(),
                    "/version" => GetVersionJson(),
                    "/playback/status" => HandlePlaybackStatus(),

                    _ => null
                };

                if (json == null && path != "/")
                {
                    ctx.Response.StatusCode = 404;
                    ctx.Response.Close();
                    return;
                }

                if (path == "/")
                {
                    json = JsonSerializer.Serialize(new
                    {
                        name = "ChoreoHelper",
                        version = GetPluginVersion(),
                        endpoints = new[] { "/actions", "/actions/emotes", "/actions/emote-durations", "/actions/races", "/dancers", "/preview", "/playback/start", "/playback/stop", "/playback/seek", "/playback/freeze", "/playback/status", "/lyrics/search", "/lyrics", "/health", "/version" }
                    }, JsonOptions);
                }
            }

            var bytes = Encoding.UTF8.GetBytes(json);
            ctx.Response.ContentLength64 = bytes.Length;
            ctx.Response.OutputStream.Write(bytes, 0, bytes.Length);
            ctx.Response.Close();
        }
        catch (Exception ex)
        {
            _log.Error(ex, "Error handling HTTP request");
            try { ctx.Response.StatusCode = 500; ctx.Response.Close(); } catch { }
        }
    }

    private void HandlePreview(HttpListenerContext ctx)
    {
        try
        {
            using var reader = new StreamReader(ctx.Request.InputStream);
            var body = reader.ReadToEnd();
            var req = System.Text.Json.JsonDocument.Parse(body);
            var command = req.RootElement.GetProperty("command").GetString() ?? "";
            AddCorsHeaders(ctx.Response);
            ctx.Response.ContentType = "application/json; charset=utf-8";
            string json;
            if (_previewer != null)
            {
                try { _previewer.Preview(command); json = JsonSerializer.Serialize(new { status = "ok", command }, JsonOptions); }
                catch { json = JsonSerializer.Serialize(new { status = "error", message = "Preview failed" }, JsonOptions); }
                // 预览顺便实测该动作的动画时长，前端用于显示/校正 clip 时长
                _freezer?.MeasureDurationDelayed(command);
            }
            else { json = JsonSerializer.Serialize(new { status = "error", message = "Previewer not available" }, JsonOptions); }
            var bytes = Encoding.UTF8.GetBytes(json);
            ctx.Response.ContentLength64 = bytes.Length;
            ctx.Response.OutputStream.Write(bytes, 0, bytes.Length);
            ctx.Response.Close();
        }
        catch (Exception ex)
        {
            _log.Error(ex, "Preview handler failed");
            ctx.Response.StatusCode = 500;
            ctx.Response.Close();
        }
    }

    private void AddCorsHeaders(HttpListenerResponse response)
    {
        foreach (var h in CorsHeaders)
        {
            var parts = h.Split([':'], 2);
            if (parts.Length == 2)
                response.Headers.Add(parts[0].Trim(), parts[1].Trim());
        }
    }

    // ===== NetEase Music API =====

    private async Task<string> SearchLyrics(string searchQuery)
    {
        try
        {
            if (string.IsNullOrWhiteSpace(searchQuery))
                return "{\"error\":\"empty query\"}";

            // If it looks like a URL with id=, extract ID and go straight to lyrics
            if (searchQuery.Contains("music.163.com") && searchQuery.Contains("id="))
            {
                var songId = ExtractSongId(searchQuery);
                if (!string.IsNullOrEmpty(songId))
                    return await GetLyrics(songId, null);
            }

            var content = new FormUrlEncodedContent(new Dictionary<string, string>
            {
                ["s"] = searchQuery,
                ["type"] = "1",
                ["limit"] = "10",
                ["offset"] = "0"
            });

            using var req = new HttpRequestMessage(HttpMethod.Post, "https://music.163.com/api/search/get")
            {
                Content = content
            };
            req.Headers.Add("Referer", "https://music.163.com");
            req.Headers.Add("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36");

            using var resp = await _httpClient.SendAsync(req);
            var json = await resp.Content.ReadAsStringAsync();
            return json;
        }
        catch (Exception ex)
        {
            _log.Error(ex, "SearchLyrics failed");
            return "{\"error\":\"" + ex.Message.Replace("\"", "\\\"") + "\"}";
        }
    }

    private async Task<string> GetLyrics(string? songId, string? url)
    {
        try
        {
            if (!string.IsNullOrEmpty(url))
            {
                songId = ExtractSongId(url) ?? songId;
            }

            if (string.IsNullOrEmpty(songId))
                return "{\"error\":\"no song id\"}";

            using var req = new HttpRequestMessage(HttpMethod.Get,
                $"https://music.163.com/api/song/lyric?os=pc&id={songId}&lv=-1&kv=-1&tv=-1");
            req.Headers.Add("Referer", "https://music.163.com");
            req.Headers.Add("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36");

            using var resp = await _httpClient.SendAsync(req);
            var json = await resp.Content.ReadAsStringAsync();
            return json;
        }
        catch (Exception ex)
        {
            _log.Error(ex, "GetLyrics failed");
            return "{\"error\":\"" + ex.Message.Replace("\"", "\\\"") + "\"}";
        }
    }

    private static string? ExtractSongId(string url)
    {
        if (string.IsNullOrEmpty(url)) return null;
        if (url.Contains("id="))
        {
            var after = url.Substring(url.IndexOf("id=") + 3);
            var id = after.Split(['&', '#', '?', '/'])[0];
            return string.IsNullOrEmpty(id) ? null : id;
        }
        return null;
    }

    // ===== Game Data Endpoints =====

    

    private string HandlePlaybackStart(HttpListenerContext ctx)
    {
        try
        {
            if (_playback == null) return "{\"error\":\"no playback\"}";
            using var reader = new StreamReader(ctx.Request.InputStream);
            var body = reader.ReadToEnd();
            var data = System.Text.Json.JsonDocument.Parse(body);
            var clips = new List<PlaybackClip>();
            if (data.RootElement.TryGetProperty("clips", out var clipsEl))
            {
                foreach (var c in clipsEl.EnumerateArray())
                {
                    clips.Add(new PlaybackClip
                    {
                        Id = c.GetProperty("id").GetInt32(),
                        Start = c.GetProperty("start").GetSingle(),
                        Duration = c.GetProperty("duration").GetSingle(),
                        Command = c.TryGetProperty("command", out var cmd) ? cmd.GetString() ?? "" : "",
                        Type = c.TryGetProperty("type", out var tp) ? tp.GetString() ?? "" : "",
                        Name = c.TryGetProperty("name", out var nm) ? nm.GetString() ?? "" : ""
                    });
                }
            }
            float fromTime = -1;
            if (data.RootElement.TryGetProperty("fromTime", out var ft) && ft.TryGetSingle(out var ftv)) fromTime = ftv;
            float speed = 1.0f;
            if (data.RootElement.TryGetProperty("speed", out var sp) && sp.TryGetSingle(out var spv)) speed = spv;
            _playback.SetSpeed(speed);
            _playback.SetTimeline(clips);
            _playback.Play(fromTime);
            return JsonSerializer.Serialize(new { status = "playing", clipCount = clips.Count }, JsonOptions);
        }
        catch (Exception ex)
        {
            _log.Error(ex, "Playback start failed");
            return "{\"error\":\"" + ex.Message.Replace("\"", "'") + "\"}";
        }
    }

    private string HandlePlaybackStop()
    {
        if (_playback == null) return "{\"error\":\"no playback\"}";
        _playback.Stop();
        return "{\"status\":\"stopped\"}";
    }

        private string HandlePlaybackFreeze(HttpListenerContext ctx)
    {
        try
        {
            if (_freezer == null) return "{\"error\":\"no freezer\"}";
            using var reader = new StreamReader(ctx.Request.InputStream);
            var body = reader.ReadToEnd();
            string command = "";
            float time = 0;
            if (!string.IsNullOrWhiteSpace(body))
            {
                try
                {
                    using var data = System.Text.Json.JsonDocument.Parse(body);
                    if (data.RootElement.TryGetProperty("command", out var cmd)) command = cmd.GetString() ?? "";
                    if (data.RootElement.TryGetProperty("time", out var t) && t.TryGetSingle(out var tv)) time = tv;
                }
                catch (Exception)
                {
                    _log.Debug("Freeze: invalid body '{body}'", body);
                    return "{\"error\":\"invalid body\"}";
                }
            }
            if (string.IsNullOrEmpty(command))
            {
                _freezer.StopPreview();
                return "{\"status\":\"unfrozen\"}";
            }
            _freezer.RequestFreezePreview(command, time);
            return JsonSerializer.Serialize(new { status = "freezing", command, time = Math.Round(time, 1) }, JsonOptions);
        }
        catch (Exception ex)
        {
            _log.Error(ex, "Freeze failed");
            return "{\"error\":\"" + ex.Message.Replace("\"", "'") + "\"}";
        }
    }

    private string HandlePlaybackSeek(HttpListenerContext ctx)
    {
        try
        {
            if (_playback == null) return "{\"error\":\"no playback\"}";
            using var reader = new StreamReader(ctx.Request.InputStream);
            var body = reader.ReadToEnd();
            float time = 0;
            if (!string.IsNullOrWhiteSpace(body))
            {
                try
                {
                    using var data = System.Text.Json.JsonDocument.Parse(body);
                    if (data.RootElement.TryGetProperty("time", out var t) && t.TryGetSingle(out var tv)) time = tv;
                }
                catch (Exception)
                {
                    _log.Debug("Seek: invalid body '{body}'", body);
                    return "{\"error\":\"invalid body\",\"hint\":\"send JSON with time field\"}";
                }
            }
            _playback.Seek(time);
            return "{\"status\":\"seeked\",\"time\":" + time.ToString("F1") + "}";
        }
        catch (Exception ex)
        {
            _log.Error(ex, "Seek failed");
            return "{\"error\":\"" + ex.Message.Replace("\"", "'") + "\"}";
        }
    }

    private string HandlePlaybackStatus()
    {
        if (_playback == null) return "{\"error\":\"no playback\"}";
        return "{\"playing\":" + (_playback.IsPlaying ? "true" : "false") + ",\"time\":" + _playback.CurrentTime.ToString("F1") + "}";
    }

    private string GetActionsJson(string? filterId)
    {
        var actions = new List<object>();
        var emoteSheet = _dataManager.GetExcelSheet<Emote>();
        if (emoteSheet != null)
        {
            foreach (var emote in emoteSheet)
            {
                var id = (int)emote.RowId;
                if (!string.IsNullOrEmpty(filterId) && id.ToString() != filterId) continue;
                var name = emote.Name.ToString();
                if (string.IsNullOrEmpty(name)) continue;
                var textCmd = "";
                try { if (emote.TextCommand.IsValid) { textCmd = emote.TextCommand.Value.Command.ToString(); } } catch { }
                var category = "";
                try { if (emote.EmoteCategory.IsValid) { category = emote.EmoteCategory.Value.Name.ToString(); } } catch { }
                actions.Add(new { id, name, command = !string.IsNullOrEmpty(textCmd) ? textCmd : "/emote", category = !string.IsNullOrEmpty(category) ? category : "通常", duration = 0f, iconId = (uint)emote.Icon, type = "emote" });
            }
        }
        var classJobSheet = _dataManager.GetExcelSheet<ClassJob>();
        var actionSheet = _dataManager.GetExcelSheet<Action>();
        if (actionSheet != null)
        {
            foreach (var action in actionSheet)
            {
                var id = (int)action.RowId;
                if (!string.IsNullOrEmpty(filterId) && id.ToString() != filterId) continue;
                var name = action.Name.ToString();
                if (string.IsNullOrEmpty(name)) continue;
                var category = "技能";
                try { if (action.ActionCategory.IsValid) { category = action.ActionCategory.Value.Name.ToString(); } } catch { }
                string animPath = "";
                try { if (action.ActionTimelineHit.IsValid) { animPath = action.ActionTimelineHit.Value.Key.ToString(); } } catch { }
                string jobName = "";
                int jobId = 0;
                try { if (action.ClassJob.IsValid) { jobName = action.ClassJob.Value.Name.ToString(); jobId = (int)action.ClassJob.RowId; } } catch { }
                string jobAbbr = "";
                try { if (action.ClassJob.IsValid) { jobAbbr = action.ClassJob.Value.Abbreviation.ToString(); } } catch { }
                if (string.IsNullOrEmpty(jobName)) continue;
                actions.Add(new { id, name, command = "/ac \"" + name + "\"", category, duration = action.Cast100ms / 100f, iconId = (uint)action.Icon, animPath, type = "action", jobName, jobId, jobAbbr });
            }
        }
        return JsonSerializer.Serialize(new { totalActions = actions.Count, gameVersion = GetGameVersion(), actions }, JsonOptions);
    }

    private string GetEmotesJson()
    {
        var emotes = new List<object>();
        var sheet = _dataManager.GetExcelSheet<Emote>();
        if (sheet != null)
        {
            foreach (var e in sheet)
            {
                var name = e.Name.ToString();
                if (string.IsNullOrEmpty(name)) continue;
                var cmd = "";
                try { if (e.TextCommand.IsValid) { cmd = e.TextCommand.Value.Command.ToString(); } } catch { }
                var category = "通常";
                try { if (e.EmoteCategory.IsValid) { var catName = e.EmoteCategory.Value.Name.ToString(); if (!string.IsNullOrEmpty(catName)) category = catName; } } catch { }
                var timelineKeys = new List<string>();
                var isLoop = false;
                try { for (uint i = 0; i < 8; i++) { var tlRef = e.ActionTimeline[(int)i]; if (tlRef.IsValid) { var key = tlRef.Value.Key.ToString(); if (!string.IsNullOrEmpty(key)) timelineKeys.Add(key); if (tlRef.Value.IsLoop) isLoop = true; } } } catch { }
                emotes.Add(new { id = (int)e.RowId, name, command = cmd, category, timelineKeys, isLoop });
            }
        }
        return JsonSerializer.Serialize(new { emotes }, JsonOptions);
    }

    private string GetEmoteDurationsJson()
    {
        var result = new List<object>();
        var emoteSheet = _dataManager.GetExcelSheet<Emote>();
        if (emoteSheet != null)
        {
            foreach (var emote in emoteSheet)
            {
                var name = emote.Name.ToString();
                if (string.IsNullOrEmpty(name)) continue;
                var timelines = new List<object>();
                try
                {
                    for (int i = 0; i < 8; i++)
                    {
                        var tlRef = emote.ActionTimeline[i];
                        if (!tlRef.IsValid) continue;
                        var tl = tlRef.Value;
                        var key = tl.Key.ToString();
                        if (string.IsNullOrEmpty(key)) continue;
                        timelines.Add(new { key, isLoop = tl.IsLoop, type = (int)tl.Type });
                    }
                }
                catch { }
                result.Add(new { id = (int)emote.RowId, name, timelines });
            }
        }
        return JsonSerializer.Serialize(new { emotes = result }, JsonOptions);
    }

    private string GetMeasuredDurationsJson()
    {
        // 实测动画时长（预览/定格/播放时累积）：{"/bow":3.2,...}
        var rounded = new Dictionary<string, float>();
        foreach (var kv in AnimationPoseFreezer.MeasuredDurations)
            rounded[kv.Key] = (float)Math.Round(kv.Value, 2);
        return JsonSerializer.Serialize(new { durations = rounded }, JsonOptions);
    }

    private string GetRacesJson()
    {
        var races = new List<object>();
        var sheet = _dataManager.GetExcelSheet<Race>();
        if (sheet != null) { foreach (var r in sheet) { races.Add(new { id = (int)r.RowId, masculine = r.Masculine.ToString(), feminine = r.Feminine.ToString() }); } }
        return JsonSerializer.Serialize(new { races }, JsonOptions);
    }

    private string GetDancersJson()
    {
        var dancers = new List<object>();
        try { if (_previewer != null) { dancers.Add(_previewer.GetLocalPlayerInfo()); } } catch (Exception ex) { _log.Error(ex, "Failed to get dancer info"); }
        return JsonSerializer.Serialize(new { dancers }, JsonOptions);
    }

    private string GetClassJobsJson()
    {
        var jobs = new List<object>();
        var sheet = _dataManager.GetExcelSheet<ClassJob>();
        if (sheet != null)
        {
            foreach (var cj in sheet)
            {
                var name = cj.Name.ToString();
                if (string.IsNullOrEmpty(name)) continue;
                var abbr = cj.Abbreviation.ToString();
                var parent = "";
                try { if (cj.ClassJobParent.IsValid) { parent = cj.ClassJobParent.Value.Name.ToString(); } } catch { }
                jobs.Add(new { id = (int)cj.RowId, name, abbreviation = abbr, parent, role = (int)cj.Role, jobIndex = (int)cj.JobIndex });
            }
        }
        return JsonSerializer.Serialize(new { classJobs = jobs }, JsonOptions);
    }
    private string GetGameVersion() { try { return _dataManager.Language.ToString(); } catch { return "unknown"; } }

    private static string GetPluginVersion()
    {
        try { return System.Reflection.Assembly.GetExecutingAssembly().GetName().Version?.ToString(3) ?? "unknown"; }
        catch { return "unknown"; }
    }

    private string GetVersionJson()
    {
        return JsonSerializer.Serialize(new { version = GetPluginVersion(), gameVersion = GetGameVersion() }, JsonOptions);
    }

    private static readonly JsonSerializerOptions JsonOptions = new() { WriteIndented = false, DefaultIgnoreCondition = JsonIgnoreCondition.WhenWritingNull };

    public void Dispose()
    {
        try { _cts?.Cancel(); } catch { }
        if (_listener != null)
        {
            try { if (_listener.IsListening) _listener.Stop(); } catch { }
            try { _listener.Close(); } catch { }
        }
        _cts?.Dispose();
        _playbackGate.Dispose();
    }
}