using System;
using System.Collections.Generic;
using System.Runtime.InteropServices;
using System.Text;
using Dalamud.Plugin.Services;
using FFXIVClientStructs.FFXIV.Client.System.Framework;
using FFXIVClientStructs.FFXIV.Client.System.String;
using FFXIVClientStructs.FFXIV.Client.UI;

namespace ChoreoHelper;

public sealed class GameCommandExecutor : IDisposable
{
    private readonly IPluginLog _log;
    private readonly IGameGui _gameGui;
    private readonly ISigScanner _sigScanner;
    private readonly IFramework _framework;
    // 队列条目带入队时间戳：出队时超时丢弃，防止积压命令无限滞后
    private readonly Queue<(string Cmd, long EnqueuedTick)> _commandQueue = new();
    private readonly object _queueLock = new();
    private const int MaxQueueSize = 64;      // 上限：防止密集 clip 无限积压
    private const long MaxQueueAgeMs = 5000;  // 出队时超过 5s 的命令视为过期丢弃

    // Delegate for ProcessChatBoxEntry (member function: thiscall in C++ terms)
    // In x64, 'this' goes in rcx, so: rcx=this(uiModule), rdx=message, r8=unused, r9b=saveToHistory
    private delegate void ProcessChatBoxEntryDelegate(nint uiModule, nint message, nint unused, byte saveToHistory);

    private ProcessChatBoxEntryDelegate? _processChatBoxEntry;
    private nint _processChatBoxEntryAddr = 0;

    public bool IsAvailable => _processChatBoxEntryAddr != 0;

    public GameCommandExecutor(IGameGui gameGui, ISigScanner sigScanner, IPluginLog log, IFramework framework)
    {
        _gameGui = gameGui;
        _sigScanner = sigScanner;
        _log = log;
        _framework = framework;
        _framework.Update += OnFrameworkUpdate;

        // Try multiple signatures
        string[] sigs = [
            "48 89 5C 24 ?? 48 89 74 24 ?? 57 48 83 EC 20 48 8B F2 48 8B F9 45 84 C9", // FFXIVClientStructs ProcessChatBoxEntry
            "48 89 5C 24 ?? 57 48 83 EC 20 48 8B FA 48 8B D9 45 84 C9",               // OOBlugin ProcessChatBox
            "48 89 5C 24 ?? 48 89 6C 24 ?? 48 89 74 24 ?? 57 48 83 EC 28 48 8B FA 48 8B F9 45 84 C9", // variant
            "4C 8B DC 49 89 5B 10 49 89 6B 18 49 89 73 20 57 48 83 EC 30 8B F2",       // another variant
        ];

        for (int i = 0; i < sigs.Length; i++)
        {
            try
            {
                var addr = _sigScanner.ScanText(sigs[i]);
                _processChatBoxEntryAddr = addr;
                _processChatBoxEntry = Marshal.GetDelegateForFunctionPointer<ProcessChatBoxEntryDelegate>(addr);
                _log.Information("[sig {i}] Found at {addr}: {sig}", i, addr, sigs[i]);
                break;
            }
            catch (Exception ex)
            {
                _log.Information("[sig {i}] Not found: {sig} ({msg})", i, sigs[i], ex.Message);
            }
        }

        if (_processChatBoxEntryAddr == 0)
        {
            _log.Error("All signatures failed! Will try FFXIVClientStructs member function as fallback.");
        }
        else
        {
            _log.Information("GameCommandExecutor: using direct delegate at {addr}", _processChatBoxEntryAddr);
        }
    }

    public void ExecuteCommand(string command)
    {
        if (string.IsNullOrWhiteSpace(command)) return;
        lock (_queueLock)
        {
            if (_commandQueue.Count >= MaxQueueSize)
            {
                _commandQueue.Dequeue(); // 队列满：丢最旧，避免无限积压
                _log.Warning("Command queue full ({n}), dropped oldest", MaxQueueSize);
            }
            _commandQueue.Enqueue((command, Environment.TickCount64));
        }
        _log.Information("Queued: {cmd}", command);
    }

    /// <summary>清空待执行队列（停止/暂停/重播时调用，防止残留命令乱执行）</summary>
    public void Clear()
    {
        lock (_queueLock)
        {
            _commandQueue.Clear();
        }
    }

    /// <summary>队列中积压的命令条数（供诊断）</summary>
    public int PendingCount
    {
        get { lock (_queueLock) { return _commandQueue.Count; } }
    }

    // 命令最小间隔：给游戏处理聊天命令留出时间，避免同帧/紧邻命令互相覆盖（吞动作）
    private static readonly TimeSpan MinCommandInterval = TimeSpan.FromMilliseconds(200);
    private DateTime _lastCommandTime = DateTime.MinValue;

    private void OnFrameworkUpdate(IFramework framework)
    {
        // 每帧至多执行一个命令，且与上一个命令至少间隔 200ms
        if ((DateTime.Now - _lastCommandTime) < MinCommandInterval) return;

        string? cmd = null;
        lock (_queueLock)
        {
            // 丢弃积压超过 MaxQueueAgeMs 的过期命令
            while (_commandQueue.Count > 0 && Environment.TickCount64 - _commandQueue.Peek().EnqueuedTick > MaxQueueAgeMs)
            {
                _commandQueue.Dequeue();
            }
            if (_commandQueue.Count > 0) cmd = _commandQueue.Dequeue().Cmd;
        }
        if (cmd == null) return;

        _lastCommandTime = DateTime.Now;
        ExecuteNow(cmd);
    }

    private unsafe void ExecuteNow(string command)
    {
        try
        {
            var framework = Framework.Instance();
            if (framework == null)
            {
                _log.Error("Framework.Instance() is null");
                return;
            }

            var uiModule = framework->GetUIModule();
            if (uiModule == null)
            {
                _log.Error("UIModule is null");
                return;
            }

            var uiModulePtr = (nint)uiModule;

            // Manually construct Utf8String (size = 0x68 = 104 bytes)
            var bytes = Encoding.UTF8.GetBytes(command + "\0");
            var len = bytes.Length - 1; // without null terminator

            // 长命令(含中文>63字节)会越出内联缓冲导致堆损坏 -> 走堆路径
            var useHeap = len >= 0x40;
            var strBuf = nint.Zero;

            var mem = Marshal.AllocHGlobal(0x68);
            // Zero-fill
            for (int i = 0; i < 0x68; i++) ((byte*)mem)[i] = 0;

            var basePtr = (byte*)mem;
            var inlineBuffer = basePtr + 0x22;

            if (useHeap)
            {
                strBuf = Marshal.AllocHGlobal(bytes.Length);
                Marshal.Copy(bytes, 0, strBuf, bytes.Length);
                // StringPtr at 0x00 → heap buffer
                *(IntPtr*)(basePtr + 0x00) = strBuf;
                // BufSize at 0x08
                *(long*)(basePtr + 0x08) = bytes.Length;
                // BufUsed at 0x10 → len + 1
                *(long*)(basePtr + 0x10) = len + 1;
                // StringLength at 0x18 → len
                *(long*)(basePtr + 0x18) = len;
                // IsEmpty at 0x20 → false
                basePtr[0x20] = 0;
                // IsUsingInlineBuffer at 0x21 → false (heap)
                basePtr[0x21] = 0;
            }
            else
            {
                // StringPtr at 0x00 → point to inline buffer
                *(IntPtr*)(basePtr + 0x00) = (IntPtr)inlineBuffer;
                // BufSize at 0x08 → 0x40 (64)
                *(long*)(basePtr + 0x08) = 0x40;
                // BufUsed at 0x10 → len + 1
                *(long*)(basePtr + 0x10) = len + 1;
                // StringLength at 0x18 → len
                *(long*)(basePtr + 0x18) = len;
                // IsEmpty at 0x20 → false
                basePtr[0x20] = 0;
                // IsUsingInlineBuffer at 0x21 → true
                basePtr[0x21] = 1;
                // Copy string bytes
                Marshal.Copy(bytes, 0, (IntPtr)inlineBuffer, bytes.Length);
            }

            // Verify
            var verifyStr = Encoding.UTF8.GetString(inlineBuffer, len);
            _log.Information("Pre-call: cmd='{cmd}' len={len} verify='{v}' uiModule=0x{ptr:X}",
                command, len, verifyStr, uiModulePtr);

            if (_processChatBoxEntry != null)
            {
                // Direct delegate call
                _processChatBoxEntry(uiModulePtr, mem, 0, 0);
                _log.Information("Direct delegate call OK for: {cmd}", command);
            }
            else
            {
                // Fallback: FFXIVClientStructs member function
                var utf8Str = (Utf8String*)mem;
                uiModule->ProcessChatBoxEntry(utf8Str, 0, false);
                _log.Information("FFXIVClientStructs fallback call OK for: {cmd}", command);
            }

            // Check if string was modified after call (indicates the function processed it)
            var postLen = *(long*)(basePtr + 0x18);
            var postUsed = *(long*)(basePtr + 0x10);
            _log.Information("Post-call: StringLength={len} BufUsed={used} (pre: len={preLen} used={preUsed})",
                postLen, postUsed, len, len + 1);

            Marshal.FreeHGlobal(mem);
            if (strBuf != nint.Zero) Marshal.FreeHGlobal(strBuf);
        }
        catch (Exception ex)
        {
            _log.Error(ex, "ExecuteNow failed: {cmd}", command);
        }
    }

    public void Dispose()
    {
        _framework.Update -= OnFrameworkUpdate;
    }
}
