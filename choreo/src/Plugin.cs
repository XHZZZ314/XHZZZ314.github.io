using System;
using Dalamud.Game.ClientState.Objects;
using Dalamud.Game.Command;
using Dalamud.Game.Gui;
using Dalamud.IoC;
using Dalamud.Plugin;
using Dalamud.Plugin.Services;
using Dalamud.Game;

namespace ChoreoHelper;

public sealed class Plugin : IDalamudPlugin
{
    [PluginService] public static IDataManager DataManager { get; private set; } = null!;
    [PluginService] public static IPluginLog Log { get; private set; } = null!;
    [PluginService] public static IChatGui Chat { get; private set; } = null!;
    [PluginService] public static IObjectTable ObjectTable { get; private set; } = null!;
    [PluginService] public static ICommandManager CommandManager { get; private set; } = null!;
    [PluginService] public static IFramework Framework { get; private set; } = null!;
    [PluginService] public static IGameGui GameGui { get; private set; } = null!;
    [PluginService] public static ISigScanner SigScanner { get; private set; } = null!;

    public string Name => "ChoreoHelper";

    private HttpServer? _httpServer;
    private ActionPreviewer? _previewer;
    private PlaybackManager? _playback;
    private GameCommandExecutor? _executor;
    private AnimationPoseFreezer? _freezer;

    public Plugin()
    {
        try
        {
            _executor = new GameCommandExecutor(GameGui, SigScanner, Log, Framework);
            _previewer = new ActionPreviewer(ObjectTable, _executor, Log);
            _freezer = new AnimationPoseFreezer(Log, ObjectTable, Framework, _executor, DataManager);
            _playback = new PlaybackManager(Log, Framework, _executor, _freezer);
            _httpServer = new HttpServer(DataManager, Log, _previewer, _playback, _freezer);
            _httpServer.Start();
            Log.Information("ChoreoHelper v0.5.21 started. API: http://localhost:48794/");
            Chat.Print("ChoreoHelper v0.5.21 已启动", "队列执行模式 + 手动 Utf8String");
        }
        catch (Exception ex)
        {
            Log.Error(ex, "Failed to start ChoreoHelper");
        }
    }

    public void Dispose()
    {
        _httpServer?.Dispose();
        _previewer?.Dispose();
        _freezer?.Dispose();
        _playback?.Dispose();
        _executor?.Dispose();
    }
}
