using System;
using Dalamud.Game.ClientState.Objects;
using Dalamud.Plugin.Services;

namespace ChoreoHelper;

public sealed class ActionPreviewer : IDisposable
{
    private readonly IObjectTable _objectTable;
    private readonly GameCommandExecutor _executor;
    private readonly IPluginLog _log;

    public ActionPreviewer(IObjectTable objectTable, GameCommandExecutor executor, IPluginLog log)
    {
        _objectTable = objectTable;
        _executor = executor;
        _log = log;
    }

    public object GetLocalPlayerInfo()
    {
        try
        {
            var player = _objectTable.LocalPlayer;
            if (player == null) return new { name = "", jobId = 0, level = 0 };
            return new
            {
                name = player.Name.ToString(),
                jobId = (int)player.ClassJob.RowId,
                level = player.Level
            };
        }
        catch { return new { name = "", jobId = 0, level = 0 }; }
    }

    public void Preview(string command)
    {
        try
        {
            _executor.ExecuteCommand(command);
        }
        catch (Exception ex) { _log.Error(ex, "Preview failed"); }
    }

    public void Dispose() { }
}
