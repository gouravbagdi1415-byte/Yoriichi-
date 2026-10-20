--====================================================================
--  Xector Kill farm  ·  ALL IN ONE  [v7 UI REDESIGN]
--  1 Auto Bypass -> 2 Auto Farm Dummy -> 3 Auto Pop Ult & Kill -> 4 End
--
--  v6 CHANGES
--   · TARGET DIES => INSTANT ROTATE (no respawn wait, no idle frames)
--   · Fallback to Dummy whenever nobody is alive (bar never stalls)
--   · Guard: Off / Rotate / Bail  (+ adjustable Min HP, right-click)
--   · Pre-rotate off targets whose Ultimate hits 100 (dodge Domains)
--   · Fire ALL ready moves per tick + M1 filler = faster meter
--   · Ragdoll-aware latch (no more physics flings)
--   · Ult/sec readout, smarter stall handling (rotate before restart)
--
--  AFK LOOP CHANGES
--   · New toggle row "5. AFK Loop" (default OFF, persisted to config)
--   · ON  : death anywhere -> wait for a FULL respawn, restart from row 1
--           full success   -> restart from row 1, forever
--           failed stage   -> restart from row 1 (short delay, no respawn wait)
--   · OFF : original single-pass behaviour, completely untouched
--   · Leave/Hop server transitions are waited out; a Leave never ends the loop
--   · Exactly one worker + one watchdog -> no duplicate automation
--
--  FIX PASS (this build)
--   · refreshWorld() used to nil Services; a cycle that never called a remote
--     left it nil and farmRoutine() bailed instantly -> fake rapid restart.
--     Now Services is re-resolved every cycle and farmRoutine refreshes too.
--   · "aborted" now means a REAL death only; genuine stage failures return
--     "fail" and retry with a short delay instead of a bogus respawn wait.
--   · waitRespawn() waits for the old character to actually die first.
--   · Watchdog only fires on a true alive->dead transition, never during an
--     intentional doReset().
--   · Minimum gap between cycle starts so the loop can never spin.
--====================================================================
print("[Xector Kill farm] 1/4 top")

local GENV0 = (type(getgenv) == "function" and getgenv()) or _G
if GENV0.EZ02_Stop then pcall(GENV0.EZ02_Stop) end
GENV0.EZ02_TOKEN = nil

local Players = game:GetService("Players")
local RS      = game:GetService("ReplicatedStorage")
local UIS     = game:GetService("UserInputService")
local RunS    = game:GetService("RunService")
local HS      = game:GetService("HttpService")
local LP      = Players.LocalPlayer

local GENV = (type(getgenv) == "function" and getgenv()) or _G
local TOKEN = {}

local _wait   = (task and task.wait) or wait
local _delay  = (task and task.delay) or delay
local _spawn  = (task and task.spawn) or function(f) coroutine.wrap(f)() end
local _unpack = table.unpack or unpack
local DEBUG   = false

--=============================== CONSTANTS ==============================
local TARGET_POS = Vector3.new(-57.3561363, 22.9888306, 488.23172)
local TARGET_CF  = CFrame.new(TARGET_POS)
local SAFE_CF    = TARGET_CF * CFrame.new(0, 6, 0)   -- [v6] regen anchor
local MAX_DIST   = 20
local CYCLES     = 3
local KIDNAP_RETURN_CF = CFrame.new(-147.833298, -30.7250881, -227.811417,
    0.970708251, -2.46936587e-08, 0.240261301,
    -2.45447391e-12, 1, 1.02788263e-07,
    -0.240261301, -9.97780063e-08, 0.970708251)
local DUMMY_NAME  = "Dummy"
local DUMMY_OFF   = CFrame.new(0, 0, 2)
local KILL_OFF    = CFrame.new(0, 0, 3)
local CLOSE_DIST  = 25
local NEARBY      = 15
local ULT_GOAL    = 100
local FARM_TICK   = 0.08
local STALL_LIMIT = 30
local CFG_FILE    = "ezconfig.txt"

-- [v5] kidnap/attach tuning
local BEHIND_OFF  = CFrame.new(0, 0, 3)   -- 3 studs behind the target
local STICK_TICK  = 0.05
local DMG_WINDOW  = 5                     -- seconds
local DMG_LIMIT   = 3                     -- hits inside window => switch
local KIDNAP_ORDER = { "Rapid Punches", "Twofold Kick", "Reversal Red" }
local KIDNAP_SVC = {
    ["Rapid Punches"] = "RapidPunchesService",
    ["Twofold Kick"]  = "TwofoldKickService",
    ["Reversal Red"]  = "ReversalRedService",
}
local MODE_ORDER = { Off = "Dummy", Dummy = "Player", Player = "Off" }
local MODE_BACK  = { Off = "Player", Player = "Dummy", Dummy = "Off" }
local GUARD_ORDER = { Off = "Rotate", Rotate = "Bail", Bail = "Off" }
local GUARD_BACK  = { Off = "Bail", Bail = "Rotate", Rotate = "Off" }
local HP_STEPS   = { 20, 30, 35, 45, 55, 65 }

-- [v6] farm pacing
local REFIRE     = 0.5    -- min gap between repeats of the same move
local M1_RATE    = 0.22   -- Gojo "Up" filler cadence
local ROTATE_MIN = 1.0    -- min dwell between non-death rotations
local BURST_HP   = 45     -- if target is under this %, stay on them to finish

-- [AFK] minimum wall time between the start of two cycles (anti-spin)
local MIN_CYCLE_GAP = 1.5

-- [AFK] row list grew by one, so the panel grew by 25px to match
local PANEL_SIZE = UDim2.new(0, 344, 0, 680)

local cfg = { AutoBypass = true, AutoFarm = true,
              KidnapMode = "Dummy", KidnapTarget = "Dummy", AvoidDomains = true,
              Guard = "Rotate", MinHealth = 35, RecoverHP = 70, FallbackDummy = true,
              AutoPopUlt = true, AutoEndAction = true,
              EndMode = "Hop", WaitForDomains = true, AFKLoop = false }
local KEYS = { "AutoBypass", "AutoFarm", "AvoidDomains", "AutoPopUlt", "AutoEndAction", "AFKLoop" }

--=============================== STATE ==================================
local running, attempts = false, 0
local cycleAbort = false     -- [AFK] the character DIED -> restart the cycle
local respawning = false     -- [AFK] we are deliberately waiting for a respawn
local leftServer = false     -- [AFK] last End Action handed us to another server
local ui = {}
local startWorker
local paintToggles, saveCfg, refreshUI, cycleTarget, autoPickTarget, stopStick
local Services
local cooldowns = { ["Rapid Punches"] = false, ["Twofold Kick"] = false, ["Reversal Red"] = false }
local watched = setmetatable({}, { __mode = "k" })

-- [v5/v6] player-target state
local blacklist = {}
local stickSelf, stickTarget, stickConn
local dmgState = { target = nil, health = nil, hits = {} }
local lastFired, lastLight, lastRotate = {}, 0, 0

local function log(...) if DEBUG then print("[Xector Kill farm]", ...) end end
local function stage(t)
    if ui.stage then
        local stagePart = tostring(t):match("^(%d+/%d+)")
        ui.stage.Text = stagePart and ("STAGE " .. stagePart .. "  •  READY") or ("STAGE  /  " .. tostring(t):upper())
    end
    print("[Xector Kill farm] " .. t)
end
local function say(t)
    t = tostring(t)
    if ui.status then ui.status.Text = "Status: " .. t end
    if DEBUG then print("[Xector Kill farm] " .. t) end
end

-- [AFK] single source of truth: are we still supposed to be doing work?
--      "running" false  = user pressed STOP
--      "cycleAbort"     = the character died / stage interrupted
local function active() return running and not cycleAbort end

--=============================== GUI ====================================
local function new(class, parent, props)
    local o = Instance.new(class)
    if props then for k, v in pairs(props) do o[k] = v end end
    if parent then o.Parent = parent end
    return o
end

local function isInstance(v)
    if v == nil then return false end
    if typeof then return typeof(v) == "Instance" end
    return type(v) == "userdata"
end

local OLD_NAMES = { "XectorKillFarm", "EZ02ScriptHub", "EZ02", "EZ_02", "EZ 0.2 SCRIPT", "EZ02AllInOne",
    "AutoBypass", "AutoBypassGUI", "AutoBypassScript", "BypassGUI",
    "AutoFarmDummy", "AutoFarmDummyGUI", "AutoFarm", "AutoFarmUlt",
    "AutoUltKill", "AutoUltKillGUI", "AutoUltAndKill", "AutoPopUlt", "AutoKill" }

local function wipeOld()
    local list = {}
    local pg = LP and LP:FindFirstChild("PlayerGui")
    if pg then table.insert(list, pg) end
    if type(gethui) == "function" then
        local ok, h = pcall(gethui)
        if ok and isInstance(h) then table.insert(list, h) end
    end
    local ok2, cg = pcall(function() return game:GetService("CoreGui") end)
    if ok2 and cg then table.insert(list, cg) end
    local n = 0
    for i = 1, #list do
        local kids = list[i]:GetChildren()
        for j = 1, #kids do
            local o = kids[j]
            if o:IsA("ScreenGui") then
                local kill = false
                pcall(function() kill = o:GetAttribute("EZ02") == true end)
                if not kill then
                    for k = 1, #OLD_NAMES do
                        if o.Name == OLD_NAMES[k] then kill = true; break end
                    end
                end
                if kill then pcall(function() o:Destroy() end); n = n + 1 end
            end
        end
    end
    return n
end

local function buildGui()
    local pg = LP and LP:WaitForChild("PlayerGui", 10)
    if not pg then
        local ok, h = pcall(gethui)
        pg = (ok and isInstance(h)) and h or nil
    end
    if not pg then error("no PlayerGui / gethui available") end

    -- Xector theme: deep navy surfaces, electric cyan accents, soft borders.
    local C = {
        panel       = Color3.fromRGB(13, 18, 30),
        panelTop    = Color3.fromRGB(21, 29, 48),
        card        = Color3.fromRGB(20, 28, 44),
        row         = Color3.fromRGB(25, 34, 52),
        rowHover    = Color3.fromRGB(31, 43, 64),
        border      = Color3.fromRGB(49, 66, 91),
        accent      = Color3.fromRGB(37, 226, 205),
        accentBlue  = Color3.fromRGB(87, 145, 255),
        purple      = Color3.fromRGB(150, 103, 255),
        green       = Color3.fromRGB(49, 220, 135),
        red         = Color3.fromRGB(255, 80, 105),
        gold        = Color3.fromRGB(255, 196, 92),
        text        = Color3.fromRGB(239, 245, 255),
        muted       = Color3.fromRGB(151, 166, 190),
        off         = Color3.fromRGB(43, 55, 75),
        white       = Color3.fromRGB(255, 255, 255),
    }
    ui.theme = C

    local sg = new("ScreenGui", pg, {
        Name = "XectorKillFarm",
        ResetOnSpawn = false,
        IgnoreGuiInset = true,
        DisplayOrder = 999,
    })
    pcall(function() sg.ZIndexBehavior = Enum.ZIndexBehavior.Sibling end)
    pcall(function() sg:SetAttribute("EZ02", true) end)
    ui.gui = sg

    local panel = new("Frame", sg, {
        Name = "Main",
        Size = PANEL_SIZE,
        AnchorPoint = Vector2.new(0.5, 0),
        Position = UDim2.new(0.5, 0, 0.055, 0),
        BackgroundColor3 = C.panel,
        BorderSizePixel = 0,
        ClipsDescendants = true,
    })
    new("UICorner", panel, { CornerRadius = UDim.new(0, 16) })
    new("UIStroke", panel, { Color = C.border, Thickness = 1.2, Transparency = 0.12 })
    new("UIGradient", panel, {
        Color = ColorSequence.new({
            ColorSequenceKeypoint.new(0, C.panelTop),
            ColorSequenceKeypoint.new(1, C.panel),
        }),
        Rotation = 90,
    })

    local topStripe = new("Frame", panel, {
        Name = "AccentStripe",
        Size = UDim2.new(1, 0, 0, 3),
        BackgroundColor3 = C.accent,
        BorderSizePixel = 0,
    })
    new("UIGradient", topStripe, {
        Color = ColorSequence.new({
            ColorSequenceKeypoint.new(0, C.accent),
            ColorSequenceKeypoint.new(0.55, C.accentBlue),
            ColorSequenceKeypoint.new(1, C.purple),
        }),
        Rotation = 0,
    })

    local header = new("Frame", panel, {
        Name = "Header",
        Position = UDim2.new(0, 0, 0, 3),
        Size = UDim2.new(1, 0, 0, 60),
        BackgroundTransparency = 1,
        Active = true,
    })
    local iconBadge = new("Frame", header, {
        Name = "BrandMark",
        Position = UDim2.new(0, 14, 0, 11),
        Size = UDim2.new(0, 38, 0, 38),
        BackgroundColor3 = Color3.fromRGB(29, 49, 66),
        BorderSizePixel = 0,
    })
    new("UICorner", iconBadge, { CornerRadius = UDim.new(0, 11) })
    new("UIStroke", iconBadge, { Color = C.accent, Thickness = 1, Transparency = 0.15 })
    new("UIGradient", iconBadge, {
        Color = ColorSequence.new(Color3.fromRGB(32, 67, 82), Color3.fromRGB(28, 36, 62)),
        Rotation = 90,
    })
    new("TextLabel", iconBadge, {
        Size = UDim2.new(1, 0, 1, 0),
        BackgroundTransparency = 1,
        Text = "X",
        TextColor3 = C.accent,
        Font = Enum.Font.GothamBlack,
        TextSize = 23,
    })

    local title = new("TextLabel", header, {
        Name = "Title",
        Position = UDim2.new(0, 62, 0, 10),
        Size = UDim2.new(1, -119, 0, 24),
        BackgroundTransparency = 1,
        Text = "Xector Kill farm",
        TextColor3 = C.text,
        Font = Enum.Font.GothamBold,
        TextSize = 17,
        TextXAlignment = Enum.TextXAlignment.Left,
        TextTruncate = Enum.TextTruncate.AtEnd,
    })
    local subtitle = new("TextLabel", header, {
        Name = "Subtitle",
        Position = UDim2.new(0, 63, 0, 34),
        Size = UDim2.new(1, -124, 0, 14),
        BackgroundTransparency = 1,
        Text = "SMART FARMING CONSOLE  /  V7",
        TextColor3 = C.muted,
        Font = Enum.Font.GothamSemibold,
        TextSize = 9,
        TextXAlignment = Enum.TextXAlignment.Left,
        TextTruncate = Enum.TextTruncate.AtEnd,
    })
    local mini = new("TextButton", header, {
        Name = "Minimize",
        Size = UDim2.new(0, 30, 0, 30),
        Position = UDim2.new(1, -44, 0, 14),
        BackgroundColor3 = C.row,
        BorderSizePixel = 0,
        AutoButtonColor = false,
        Text = "−",
        TextColor3 = C.text,
        Font = Enum.Font.GothamBold,
        TextSize = 20,
    })
    new("UICorner", mini, { CornerRadius = UDim.new(0, 9) })
    new("UIStroke", mini, { Color = C.border, Thickness = 1, Transparency = 0.15 })

    -- Live status card.
    local statusCard = new("Frame", panel, {
        Name = "StatusCard",
        Position = UDim2.new(0, 12, 0, 69),
        Size = UDim2.new(1, -24, 0, 62),
        BackgroundColor3 = C.card,
        BorderSizePixel = 0,
    })
    new("UICorner", statusCard, { CornerRadius = UDim.new(0, 11) })
    new("UIStroke", statusCard, { Color = C.border, Thickness = 1, Transparency = 0.35 })
    local liveDot = new("Frame", statusCard, {
        Name = "LiveDot",
        Position = UDim2.new(0, 14, 0, 14),
        Size = UDim2.new(0, 7, 0, 7),
        BackgroundColor3 = C.green,
        BorderSizePixel = 0,
    })
    new("UICorner", liveDot, { CornerRadius = UDim.new(1, 0) })
    ui.liveDot = liveDot

    ui.stage = new("TextLabel", statusCard, {
        Size = UDim2.new(1, -38, 0, 15),
        Position = UDim2.new(0, 29, 0, 9),
        BackgroundTransparency = 1,
        Text = "STAGE 1/4  •  READY",
        TextColor3 = C.accent,
        Font = Enum.Font.GothamBold,
        TextSize = 10,
        TextXAlignment = Enum.TextXAlignment.Left,
        TextTruncate = Enum.TextTruncate.AtEnd,
    })
    ui.status = new("TextLabel", statusCard, {
        Size = UDim2.new(1, -26, 0, 29),
        Position = UDim2.new(0, 13, 0, 27),
        BackgroundTransparency = 1,
        Text = "Status: idle",
        TextColor3 = C.text,
        Font = Enum.Font.Gotham,
        TextSize = 11,
        TextWrapped = true,
        TextXAlignment = Enum.TextXAlignment.Left,
        TextYAlignment = Enum.TextYAlignment.Center,
    })

    -- Compact telemetry card.
    local stats = new("Frame", panel, {
        Name = "TelemetryCard",
        Position = UDim2.new(0, 12, 0, 138),
        Size = UDim2.new(1, -24, 0, 52),
        BackgroundColor3 = C.card,
        BorderSizePixel = 0,
    })
    new("UICorner", stats, { CornerRadius = UDim.new(0, 11) })
    new("UIStroke", stats, { Color = C.border, Thickness = 1, Transparency = 0.35 })
    new("Frame", stats, {
        Name = "Divider",
        Position = UDim2.new(0, 130, 0, 9),
        Size = UDim2.new(0, 1, 1, -18),
        BackgroundColor3 = C.border,
        BorderSizePixel = 0,
    })
    ui.attempts = new("TextLabel", stats, {
        Size = UDim2.new(0, 121, 1, -8),
        Position = UDim2.new(0, 5, 0, 4),
        BackgroundTransparency = 1,
        Text = "Bypass Attempts: 0",
        TextColor3 = C.gold,
        Font = Enum.Font.GothamSemibold,
        TextSize = 10,
        TextWrapped = true,
        TextXAlignment = Enum.TextXAlignment.Center,
        TextYAlignment = Enum.TextYAlignment.Center,
    })
    ui.ult = new("TextLabel", stats, {
        Size = UDim2.new(1, -144, 1, -8),
        Position = UDim2.new(0, 139, 0, 4),
        BackgroundTransparency = 1,
        Text = "Ultimate: 0% / 100%",
        TextColor3 = C.accentBlue,
        Font = Enum.Font.GothamSemibold,
        TextSize = 10,
        TextWrapped = true,
        TextXAlignment = Enum.TextXAlignment.Left,
        TextYAlignment = Enum.TextYAlignment.Center,
    })

    -- Scrollable controls ensure the panel remains usable on smaller screens.
    local controls = new("ScrollingFrame", panel, {
        Name = "Controls",
        Position = UDim2.new(0, 12, 0, 200),
        Size = UDim2.new(1, -24, 0, 414),
        BackgroundTransparency = 1,
        BorderSizePixel = 0,
        CanvasSize = UDim2.new(0, 0, 0, 404),
        ScrollBarThickness = 3,
        ScrollBarImageColor3 = C.accent,
        ScrollingDirection = Enum.ScrollingDirection.Y,
        VerticalScrollBarInset = Enum.ScrollBarInset.ScrollBar,
    })
    local content = new("Frame", controls, {
        Name = "Content",
        Size = UDim2.new(1, -5, 0, 404),
        BackgroundTransparency = 1,
        BorderSizePixel = 0,
    })

    local function section(text, y)
        return new("TextLabel", content, {
            Size = UDim2.new(1, -4, 0, 14),
            Position = UDim2.new(0, 2, 0, y),
            BackgroundTransparency = 1,
            Text = text,
            TextColor3 = C.muted,
            Font = Enum.Font.GothamBold,
            TextSize = 9,
            TextXAlignment = Enum.TextXAlignment.Left,
        })
    end
    local function divider(y)
        new("Frame", content, {
            Size = UDim2.new(1, -8, 0, 1),
            Position = UDim2.new(0, 4, 0, y),
            BackgroundColor3 = C.border,
            BackgroundTransparency = 0.35,
            BorderSizePixel = 0,
        })
    end
    local function styledButton(name, text, y, h)
        local b = new("TextButton", content, {
            Name = name,
            Size = UDim2.new(1, -2, 0, h or 27),
            Position = UDim2.new(0, 1, 0, y),
            BackgroundColor3 = C.row,
            BorderSizePixel = 0,
            AutoButtonColor = false,
            Text = text,
            TextColor3 = C.text,
            Font = Enum.Font.GothamSemibold,
            TextSize = 11,
            TextXAlignment = Enum.TextXAlignment.Left,
        })
        new("UICorner", b, { CornerRadius = UDim.new(0, 8) })
        local stroke = new("UIStroke", b, { Color = C.border, Thickness = 1, Transparency = 0.2 })
        return b, stroke
    end

    section("AUTOMATION OPTIONS", 2)
    ui.toggles = {}
    ui.toggleKnobs = {}
    local rows = {
        { k = "AutoBypass",    t = "01   Auto bypass" },
        { k = "AutoFarm",      t = "02   Auto farm ultimate" },
        { k = "AvoidDomains",  t = "     Avoid domains" },
        { k = "AutoPopUlt",    t = "03   Auto pop ultimate & kill" },
        { k = "AutoEndAction", t = "04   End action when complete" },
        { k = "AFKLoop",       t = "05   AFK loop" },
    }
    for i = 1, #rows do
        local d = rows[i]
        local y = 20 + (i - 1) * 31
        local row = new("Frame", content, {
            Name = "Toggle_" .. d.k,
            Size = UDim2.new(1, -2, 0, 28),
            Position = UDim2.new(0, 1, 0, y),
            BackgroundColor3 = C.row,
            BorderSizePixel = 0,
        })
        new("UICorner", row, { CornerRadius = UDim.new(0, 8) })
        new("UIStroke", row, { Color = C.border, Thickness = 1, Transparency = 0.55 })
        new("TextLabel", row, {
            Size = UDim2.new(1, -60, 1, 0),
            Position = UDim2.new(0, 11, 0, 0),
            BackgroundTransparency = 1,
            Text = d.t,
            TextColor3 = (d.k == "AvoidDomains") and C.muted or C.text,
            Font = Enum.Font.GothamMedium,
            TextSize = 11,
            TextXAlignment = Enum.TextXAlignment.Left,
            TextTruncate = Enum.TextTruncate.AtEnd,
        })
        local box = new("TextButton", row, {
            Name = "Switch",
            Size = UDim2.new(0, 38, 0, 21),
            Position = UDim2.new(1, -47, 0.5, -10.5),
            BackgroundColor3 = C.off,
            BorderSizePixel = 0,
            AutoButtonColor = false,
            Text = "",
        })
        new("UICorner", box, { CornerRadius = UDim.new(1, 0) })
        local knob = new("Frame", box, {
            Name = "Knob",
            Size = UDim2.new(0, 15, 0, 15),
            Position = UDim2.new(0, 3, 0.5, -7.5),
            BackgroundColor3 = C.white,
            BorderSizePixel = 0,
        })
        new("UICorner", knob, { CornerRadius = UDim.new(1, 0) })
        ui.toggles[d.k] = box
        ui.toggleKnobs[d.k] = knob
        box.Activated:Connect(function()
            cfg[d.k] = not cfg[d.k]
            if d.k == "AFKLoop" then
                if cfg.AFKLoop then
                    say("AFK Loop enabled - will repeat after each cycle")
                elseif running then
                    say("AFK Loop disabled - stopping after this cycle")
                end
            end
            paintToggles()
            saveCfg()
        end)
    end

    divider(210)
    section("TARGET CONTROL", 218)

    ui.kidnap, ui.kidnapStroke = styledButton("KidnapMode", "MODE  /  " .. cfg.KidnapMode, 238, 27)
    ui.kidnap.MouseButton1Click:Connect(function()
        cfg.KidnapMode = MODE_ORDER[cfg.KidnapMode] or "Off"
        if cfg.KidnapMode == "Player" then
            if autoPickTarget then autoPickTarget() end
        else
            if stopStick then stopStick() end
        end
        refreshUI(); saveCfg()
    end)
    ui.kidnap.MouseButton2Click:Connect(function()
        cfg.KidnapMode = MODE_BACK[cfg.KidnapMode] or "Off"
        if cfg.KidnapMode ~= "Player" and stopStick then stopStick() end
        refreshUI(); saveCfg()
    end)

    ui.target, ui.targetStroke = styledButton("KidnapTarget", "TARGET  /  " .. tostring(cfg.KidnapTarget), 270, 27)
    ui.target.MouseButton1Click:Connect(function() cycleTarget(1) end)
    ui.target.MouseButton2Click:Connect(function() cycleTarget(-1) end)

    ui.guard, ui.guardStroke = styledButton("Guard", "HEALTH GUARD  /  " .. cfg.Guard, 302, 27)
    ui.guard.MouseButton1Click:Connect(function()
        cfg.Guard = GUARD_ORDER[cfg.Guard] or "Off"
        refreshUI(); saveCfg()
    end)
    ui.guard.MouseButton2Click:Connect(function()
        local idx = 1
        for i = 1, #HP_STEPS do
            if HP_STEPS[i] == cfg.MinHealth then idx = i; break end
        end
        idx = (idx % #HP_STEPS) + 1
        cfg.MinHealth = HP_STEPS[idx]
        refreshUI(); saveCfg()
    end)

    divider(338)
    section("AFTER COMPLETION", 346)
    ui.mode, ui.modeStroke = styledButton("EndMode", "END ACTION  /  " .. cfg.EndMode, 366, 27)
    ui.mode.MouseButton1Click:Connect(function()
        cfg.EndMode = (cfg.EndMode == "Hop") and "Leave" or "Hop"
        refreshUI()
        saveCfg()
    end)

    ui.start = new("TextButton", panel, {
        Name = "StartStop",
        Size = UDim2.new(1, -24, 0, 42),
        Position = UDim2.new(0, 12, 0, 625),
        BackgroundColor3 = C.green,
        BorderSizePixel = 0,
        AutoButtonColor = false,
        Text = "START AUTOMATION",
        TextColor3 = C.white,
        Font = Enum.Font.GothamBold,
        TextSize = 13,
    })
    new("UICorner", ui.start, { CornerRadius = UDim.new(0, 11) })
    ui.startGradient = new("UIGradient", ui.start, {
        Color = ColorSequence.new(Color3.fromRGB(39, 205, 132), Color3.fromRGB(25, 157, 133)),
        Rotation = 0,
    })
    new("UIStroke", ui.start, { Color = Color3.fromRGB(105, 255, 194), Thickness = 1, Transparency = 0.38 })

    -- Drag from the title area on mouse or touch.
    local drag, ds, sp
    title.InputBegan:Connect(function(input)
        if input.UserInputType == Enum.UserInputType.MouseButton1
            or input.UserInputType == Enum.UserInputType.Touch then
            drag, ds, sp = true, input.Position, panel.Position
            input.Changed:Connect(function()
                if input.UserInputState == Enum.UserInputState.End then drag = false end
            end)
        end
    end)
    if ui.dragConn then pcall(function() ui.dragConn:Disconnect() end) end
    ui.dragConn = UIS.InputChanged:Connect(function(input)
        if drag and (input.UserInputType == Enum.UserInputType.MouseMovement
            or input.UserInputType == Enum.UserInputType.Touch) then
            local d = input.Position - ds
            panel.Position = UDim2.new(sp.X.Scale, sp.X.Offset + d.X, sp.Y.Scale, sp.Y.Offset + d.Y)
        end
    end)

    local collapsed = false
    mini.MouseButton1Click:Connect(function()
        collapsed = not collapsed
        panel.Size = collapsed and UDim2.new(0, 344, 0, 63) or PANEL_SIZE
        mini.Text = collapsed and "+" or "−"
        for _, child in ipairs(panel:GetChildren()) do
            if child:IsA("GuiObject") and child ~= header and child ~= topStripe then
                child.Visible = not collapsed
            end
        end
    end)
end

local wiped = 0
local guiOk, guiErr = pcall(function()
    wiped = wipeOld()
    buildGui()
end)

if not guiOk then
    print("[Xector Kill farm] GUI FAILED: " .. tostring(guiErr))
    pcall(function()
        local pg = LP:WaitForChild("PlayerGui", 5)
        if not pg then return end
        local sg = new("ScreenGui", pg, { Name = "XectorKillFarm", ResetOnSpawn = false })
        local f = new("Frame", sg, { Size = UDim2.new(0, 340, 0, 110),
            Position = UDim2.new(0.5, -170, 0.2, 0), BackgroundColor3 = Color3.fromRGB(25, 25, 25) })
        new("TextLabel", f, { Size = UDim2.new(1, -10, 1, -10), Position = UDim2.new(0, 5, 0, 5),
            BackgroundTransparency = 1, TextWrapped = true, Font = Enum.Font.Code, TextSize = 12,
            TextColor3 = Color3.fromRGB(255, 90, 90), Text = "Xector Kill farm UI error:\n" .. tostring(guiErr) })
    end)
end

stage("2/4 gui ok (wiped " .. wiped .. ")")

paintToggles = function()
    if not ui.toggles then return end
    local C = ui.theme or {}
    for i = 1, #KEYS do
        local key = KEYS[i]
        local b = ui.toggles[key]
        local knob = ui.toggleKnobs and ui.toggleKnobs[key]
        local enabled = cfg[key] == true
        if b then
            b.BackgroundColor3 = enabled and (C.accent or Color3.fromRGB(37, 226, 205))
                or (C.off or Color3.fromRGB(43, 55, 75))
        end
        if knob then
            knob.Position = enabled and UDim2.new(1, -18, 0.5, -7.5)
                or UDim2.new(0, 3, 0.5, -7.5)
            knob.BackgroundColor3 = enabled and (C.white or Color3.new(1, 1, 1))
                or Color3.fromRGB(190, 201, 218)
        end
    end
    if ui.mode then ui.mode.Text = "END ACTION  /  " .. cfg.EndMode end
end

refreshUI = function()
    local C = ui.theme or {}
    if ui.start then
        ui.start.Text = running and "STOP AUTOMATION" or "START AUTOMATION"
        ui.start.BackgroundColor3 = running and (C.red or Color3.fromRGB(255, 80, 105))
            or (C.green or Color3.fromRGB(49, 220, 135))
        if ui.startGradient then
            ui.startGradient.Color = running
                and ColorSequence.new(Color3.fromRGB(255, 83, 112), Color3.fromRGB(199, 48, 84))
                or ColorSequence.new(Color3.fromRGB(39, 205, 132), Color3.fromRGB(25, 157, 133))
        end
    end
    if ui.liveDot then
        ui.liveDot.BackgroundColor3 = running
            and (C.green or Color3.fromRGB(49, 220, 135))
            or (C.accent or Color3.fromRGB(37, 226, 205))
    end
    paintToggles()
    if ui.kidnap then
        ui.kidnap.Text = "MODE  /  " .. cfg.KidnapMode
        ui.kidnap.TextColor3 = (cfg.KidnapMode == "Off")
            and (C.muted or Color3.fromRGB(151, 166, 190))
            or (C.accent or Color3.fromRGB(37, 226, 205))
        ui.kidnap.BackgroundColor3 = C.row or Color3.fromRGB(25, 34, 52)
        if ui.kidnapStroke then
            ui.kidnapStroke.Color = (cfg.KidnapMode == "Off")
                and (C.border or Color3.fromRGB(49, 66, 91))
                or (C.accent or Color3.fromRGB(37, 226, 205))
        end
    end
    if ui.target then
        ui.target.Text = "TARGET  /  " .. tostring(cfg.KidnapTarget)
        local on = cfg.KidnapMode == "Player"
        ui.target.TextColor3 = on and (C.accentBlue or Color3.fromRGB(87, 145, 255))
            or (C.muted or Color3.fromRGB(151, 166, 190))
        ui.target.BackgroundColor3 = C.row or Color3.fromRGB(25, 34, 52)
        if ui.targetStroke then
            ui.targetStroke.Color = on and (C.accentBlue or Color3.fromRGB(87, 145, 255))
                or (C.border or Color3.fromRGB(49, 66, 91))
        end
    end
    if ui.guard then
        ui.guard.Text = ("HEALTH GUARD  /  %s  ·  %d%%"):format(cfg.Guard, cfg.MinHealth)
        ui.guard.TextColor3 = (cfg.Guard == "Off")
            and (C.muted or Color3.fromRGB(151, 166, 190))
            or (C.green or Color3.fromRGB(49, 220, 135))
        ui.guard.BackgroundColor3 = C.row or Color3.fromRGB(25, 34, 52)
        if ui.guardStroke then
            ui.guardStroke.Color = (cfg.Guard == "Off")
                and (C.border or Color3.fromRGB(49, 66, 91))
                or (C.green or Color3.fromRGB(49, 220, 135))
        end
    end
    if ui.mode then
        ui.mode.Text = "END ACTION  /  " .. cfg.EndMode
        ui.mode.TextColor3 = C.accentBlue or Color3.fromRGB(87, 145, 255)
        if ui.modeStroke then ui.modeStroke.Color = C.accentBlue or Color3.fromRGB(87, 145, 255) end
    end
end

saveCfg = function()
    if not (writefile and isfile) then return end
    local t = {}
    for i = 1, #KEYS do t[KEYS[i]] = cfg[KEYS[i]] end
    pcall(function() writefile(CFG_FILE, HS:JSONEncode({
        Toggles = t, Mode = cfg.EndMode,
        KidnapMode = cfg.KidnapMode, KidnapTarget = cfg.KidnapTarget,
        Guard = cfg.Guard, MinHealth = cfg.MinHealth })) end)
end

local function loadCfg()
    if not (readfile and isfile and isfile(CFG_FILE)) then return end
    local ok, data = pcall(function() return HS:JSONDecode(readfile(CFG_FILE)) end)
    if not ok or type(data) ~= "table" then return end
    if type(data.Toggles) == "table" then
        for k, v in pairs(data.Toggles) do
            if cfg[k] ~= nil and type(v) == "boolean" then cfg[k] = v end
        end
        if data.KidnapMode == nil and data.Toggles.AutoKidnap ~= nil then
            cfg.KidnapMode = data.Toggles.AutoKidnap and "Dummy" or "Off"
        end
    end
    if data.Mode == "Hop" or data.Mode == "Leave" then cfg.EndMode = data.Mode end
    if data.KidnapMode == "Off" or data.KidnapMode == "Dummy" or data.KidnapMode == "Player" then
        cfg.KidnapMode = data.KidnapMode
    end
    if type(data.KidnapTarget) == "string" then cfg.KidnapTarget = data.KidnapTarget end
    if data.Guard == "Off" or data.Guard == "Rotate" or data.Guard == "Bail" then
        cfg.Guard = data.Guard
    end
    if type(data.MinHealth) == "number" and data.MinHealth >= 5 and data.MinHealth <= 90 then
        cfg.MinHealth = math.floor(data.MinHealth)
    end
end

--=============================== SERVICES ===============================
local function getSvcFolder()
    local k = RS and RS:FindFirstChild("Knit")
    if not k then return nil end
    local inner = k:FindFirstChild("Knit")
    return (inner and inner:FindFirstChild("Services")) or k:FindFirstChild("Services")
end

local function refreshServices()
    Services = getSvcFolder()
    if not Services then
        local d = RS:GetDescendants()
        for i = 1, #d do
            if d[i].Name == "Services" then Services = d[i]; break end
        end
    end
    return Services
end

local function getRemote(s, r)
    if not Services or not Services.Parent then refreshServices() end
    if not Services then return nil end
    local svc = Services:FindFirstChild(s)
    local re = svc and svc:FindFirstChild("RE")
    local rem = re and re:FindFirstChild(r)
    if rem and rem:IsA("RemoteEvent") then return rem end
    return nil
end

local function fire(s, r, ...)
    local rem = getRemote(s, r)
    if not rem then return false end
    local n = select("#", ...)
    local a = { ... }
    return pcall(function()
        if n == 0 then rem:FireServer() else rem:FireServer(_unpack(a, 1, n)) end
    end)
end

local function tryMove(c, moveName)
    local svc = KIDNAP_SVC[moveName]
    if not svc then return false end
    local ms = c and c:FindFirstChild("Moveset")
    local mv = ms and ms:FindFirstChild(moveName)
    if not mv then return false end

    -- fire() returns false if the remote cannot be found or FireServer errors.
    -- Do not mark the move as fired unless the remote call actually succeeded.
    local ok = fire(svc, "Activated", mv, nil)
    return ok == true
end

--=============================== CHARACTER ==============================
local function getChar()
    local lp = LP
    if not lp then return nil end
    local c = lp.Character
    if not c or not c.Parent then
        local cs = workspace:FindFirstChild("Characters")
        if cs then c = cs:FindFirstChild(lp.Name) end
    end
    return c
end

local function getHRP(c) c = c or getChar(); return c and c:FindFirstChild("HumanoidRootPart") end
local function getInfo(c) c = c or getChar(); return c and c:FindFirstChild("Info") end
local function getDummy()
    local cs = workspace:FindFirstChild("Characters")
    return cs and cs:FindFirstChild(DUMMY_NAME)
end
local function getUlt()
    if not LP then return 0 end
    return tonumber(LP:GetAttribute("Ultimate")) or 0
end

local function hpPct(h)
    h = h or (getChar() and getChar():FindFirstChildOfClass("Humanoid"))
    if not h then return 100 end
    local mx = (h.MaxHealth > 0) and h.MaxHealth or 100
    return (h.Health / mx) * 100
end

local function isRagdoll(c)
    c = c or getChar()
    return c ~= nil and c:FindFirstChild("RagdollConstraints") ~= nil
end

-- [AFK] is the character present and alive right now? (death detection)
local function characterAlive()
    local c = getChar()
    if not c or not c.Parent then return false end
    local h = c:FindFirstChildOfClass("Humanoid")
    return h ~= nil and h.Health > 0
end

-- [AFK] alive AND standing (safe to actually start a stage)
local function stageReady()
    if not characterAlive() then return false end
    local c = getChar()
    return c:FindFirstChild("RagdollConstraints") == nil
end

--=============================== TARGETING ==============================
local function inDomain(model)
    local folder = workspace:FindFirstChild("Domains")
    if not folder then return false end
    local hrp = model and model:FindFirstChild("HumanoidRootPart")
    if not hrp then return false end
    local pos = hrp.Position
    local kids = folder:GetChildren()
    for i = 1, #kids do
        local dom = kids[i]
        local ok, inside = pcall(function()
            local cf, size
            if dom:IsA("BasePart") then
                cf, size = dom.CFrame, dom.Size
            elseif dom:IsA("Model") then
                cf, size = dom:GetBoundingBox()
            else
                return false
            end
            local rel = cf:PointToObjectSpace(pos)
            local h = size * 0.5
            return math.abs(rel.X) <= h.X and math.abs(rel.Y) <= h.Y and math.abs(rel.Z) <= h.Z
        end)
        if ok and inside then return true end
    end
    return false
end

-- [v6] score = distance, penalised by target health (prefer hurt targets so
-- we actually KILL and bank meter), by a ready enemy Ultimate (incoming
-- Domain), and rewarded if they're already distracted by someone else.
local function scoreTarget(p, myPos, useBlacklist)
    if p == LP then return nil end
    local ch = p.Character
    local hrp = ch and ch:FindFirstChild("HumanoidRootPart")
    local hum = ch and ch:FindFirstChildOfClass("Humanoid")
    if not (hrp and hum and hum.Health > 0) then return nil end
    if cfg.AvoidDomains and inDomain(ch) then return nil end
    if useBlacklist then
        local bl = blacklist[p.Name]
        if bl and bl > os.clock() then return nil end
    end
    local s = (hrp.Position - myPos).Magnitude
    s = s - (100 - hpPct(hum)) * 0.4            -- hurt targets first
    if (tonumber(p:GetAttribute("Ultimate")) or 0) >= 100 then s = s + 30 end
    -- distracted? another player within 12 studs of them
    local plrs = Players:GetPlayers()
    for i = 1, #plrs do
        local o = plrs[i]
        if o ~= LP and o ~= p then
            local orp = o.Character and o.Character:FindFirstChild("HumanoidRootPart")
            if orp and (orp.Position - hrp.Position).Magnitude <= 12 then s = s - 8; break end
        end
    end
    return s
end

local function scanTargets(skip, useBlacklist)
    local myRoot = getHRP()
    local myPos = myRoot and myRoot.Position or TARGET_POS
    local best, bestS
    local plrs = Players:GetPlayers()
    for i = 1, #plrs do
        local p = plrs[i]
        if p.Name ~= skip then
            local s = scoreTarget(p, myPos, useBlacklist)
            if s and (not bestS or s < bestS) then best, bestS = p.Name, s end
        end
    end
    return best
end

local function nextTarget(skip)
    return scanTargets(skip, true) or scanTargets(skip, false)
end

local function validTargets(skipName)
    local myRoot = getHRP()
    local myPos = myRoot and myRoot.Position or TARGET_POS
    local out = {}
    local plrs = Players:GetPlayers()
    for i = 1, #plrs do
        local p = plrs[i]
        if p.Name ~= skipName then
            local s = scoreTarget(p, myPos, false)
            if s then out[#out + 1] = { name = p.Name, s = s } end
        end
    end
    table.sort(out, function(a, b) return a.s < b.s end)
    local names = {}
    for i = 1, #out do names[i] = out[i].name end
    return names
end

local function snapBehind(root, troot)
    if not root or not troot or not root.Parent or not troot.Parent then return end
    local behind = troot.CFrame * BEHIND_OFF
    root.CFrame = CFrame.lookAt(behind.Position,
        Vector3.new(troot.Position.X, behind.Position.Y, troot.Position.Z))
end

-- [v6] instant rotation: pick next best and snap there the SAME frame
local function rotateTarget(reason, skip)
    local nxt = nextTarget(skip)
    if not nxt then
        stopStick()
        return false
    end

    cfg.KidnapTarget = nxt
    dmgState.target = nil
    local p = Players:FindFirstChild(nxt)
    local troot = p and p.Character and p.Character:FindFirstChild("HumanoidRootPart")
    local root = getHRP()

    -- Apply the first snap immediately, then keep the Heartbeat latch attached.
    if root and troot then
        stickSelf, stickTarget = root, troot
        snapBehind(root, troot)
    else
        stopStick()
    end

    lastRotate = os.clock()
    say(("Rotate -> %s (%s)"):format(nxt, reason))
    if refreshUI then refreshUI() end
    if saveCfg then saveCfg() end
    return true
end

autoPickTarget = function(skip)
    local names = validTargets(skip)
    if #names == 0 then return false end
    cfg.KidnapTarget = names[1]
    if refreshUI then refreshUI() end
    if saveCfg then saveCfg() end
    return true
end

cycleTarget = function(dir)
    local list = { "Dummy" }
    local names = validTargets(nil)
    for i = 1, #names do list[#list + 1] = names[i] end
    local idx = 1
    for i = 1, #list do
        if list[i] == cfg.KidnapTarget then idx = i; break end
    end
    idx = idx + (dir or 1)
    if idx > #list then idx = 1 end
    if idx < 1 then idx = #list end
    cfg.KidnapTarget = list[idx]
    refreshUI(); saveCfg()
end

local function resolveTarget()
    if cfg.KidnapMode == "Dummy" then return getDummy(), "Dummy" end
    if cfg.KidnapMode ~= "Player" then return nil, nil end

    local name = cfg.KidnapTarget
    if not name or name == "Dummy" then
        name = nextTarget()
        if not name then return nil, nil end
        cfg.KidnapTarget = name
    end

    local p = Players:FindFirstChild(name)
    local ch = p and p.Character
    if not ch then
        -- A saved target may have left or may still be respawning. Try another
        -- valid target rather than idling on a stale name until the farm stalls.
        local replacement = nextTarget(name)
        if replacement then
            cfg.KidnapTarget = replacement
            if refreshUI then refreshUI() end
            if saveCfg then saveCfg() end
            local rp = Players:FindFirstChild(replacement)
            ch = rp and rp.Character
            name = replacement
        end
    end
    -- Deliberately leave health/root/Domain validation to playerKidnapTick so
    -- its target-died and Domain-rotation handlers can actually run.
    return ch, name
end

-- Heartbeat latch. Reacquire our root after respawns and guard against stale parts.
local function stickHandler()
    if not running then return end

    local r, t = stickSelf, stickTarget
    if not t or not t.Parent then
        stickSelf, stickTarget = nil, nil
        return
    end

    local currentRoot = getHRP()
    if currentRoot and currentRoot ~= r then
        r = currentRoot
        stickSelf = currentRoot
    end
    if not r or not r.Parent or not t.Parent then return end
    if isRagdoll() then return end

    -- Reuse the same placement logic as the immediate snap; isolate transient
    -- character-removal errors so one bad frame does not break the latch.
    pcall(function() snapBehind(r, t) end)
end

stickConn = RunS.Heartbeat:Connect(stickHandler)

stopStick = function()
    stickSelf, stickTarget = nil, nil
    local h = getChar() and getChar():FindFirstChildOfClass("Humanoid")
    if h then pcall(function() h.AutoRotate = true end) end
end

local resetRemote
local function getReset()
    if resetRemote and resetRemote.Parent then return resetRemote end
    resetRemote = getRemote("JoinService", "Reset")
    if resetRemote then return resetRemote end
    local d = RS:GetDescendants()
    for i = 1, #d do
        local x = d[i]
        if x.Name == "Reset" and x:IsA("RemoteEvent") and x.Parent and x.Parent.Name == "RE" then
            resetRemote = x
            return x
        end
    end
    return nil
end

local function doReset()
    local rem = getReset()
    if rem then pcall(function() rem:FireServer() end); return "remote" end
    local c = getChar()
    local h = c and c:FindFirstChildOfClass("Humanoid")
    if h then pcall(function() h.Health = 0 end); return "humanoid" end
    return nil
end

--=============================== STEP 1: BYPASS =========================
-- [AFK] robust respawn wait.
--   expectDeath = true  -> first let the old character actually die (covers
--                          our own intentional reset), THEN wait for the new one
--   expectDeath = false -> the character is already gone; just wait for a live one
-- Returns true only when a real, standing character is back.
local function waitRespawn(expectDeath)
    if respawning then return running end
    respawning = true
    say("Waiting for respawn...")

    local t0 = os.clock()
    if expectDeath then
        while running and characterAlive() and os.clock() - t0 < 3 do
            _wait(0.05)
        end
    end

    local start = os.clock()
    local lastNudge = start
    local aliveSince = nil
    while running do
        if characterAlive() then
            aliveSince = aliveSince or os.clock()
            local rag = isRagdoll()
            -- accept immediately when standing; otherwise give a ragdoll 2s to clear
            if (not rag) or (os.clock() - aliveSince > 2) then
                _wait(0.2)
                if characterAlive() then
                    say("Respawn complete.")
                    respawning = false
                    leftServer = false
                    return true
                end
            end
        else
            aliveSince = nil
        end
        local now = os.clock()
        if now - start > 8 and now - lastNudge > 8 then
            lastNudge = now
            say("Respawn slow - forcing reset...")
            doReset()
            _wait(0.3)
        end
        _wait(0.1)
    end
    respawning = false
    return false
end

local function cycles()
    for i = 1, CYCLES do
        if not active() then return false end
        local c = getChar()
        local hrp = getHRP(c)
        if not c or not hrp then _wait(1); return false end
        say(("Bypass Cycle %d/%d..."):format(i, CYCLES))
        c:PivotTo(TARGET_CF)
        _wait(0.2)
        hrp = getHRP()
        local dist = hrp and (hrp.Position - TARGET_POS).Magnitude
        log(("cycle %d dist %s"):format(i, dist and ("%.1f"):format(dist) or "nil"))
        if not (hrp and dist and dist <= MAX_DIST) then
            say("Rubberbanded. Resetting...")
            return false
        end
        say(("Cycle %d: OK"):format(i))
        _wait(0.1)
    end
    return true
end

local function waitDomains()
    if not workspace:FindFirstChild("Domains") then return end
    while active() do
        local d = workspace:FindFirstChild("Domains")
        if not d or #d:GetChildren() == 0 then break end
        say("Waiting for Domain to clear...")
        _wait(0.5)
    end
    if active() then say("Domain cleared."); _wait(0.2) end
end

local function bypassRoutine()
    attempts = 0
    if ui.attempts then ui.attempts.Text = "Bypass Attempts: 0" end
    while active() do
        attempts = attempts + 1
        if ui.attempts then ui.attempts.Text = "Bypass Attempts: " .. attempts end
        if cycles() then
            say("Bypass completed.")
            _wait(1)
            if cfg.WaitForDomains then waitDomains() end
            return true
        end
        if not active() then return false end   -- died mid-cycle: let the loop restart

        -- Our own reset. waitRespawn(true) marks "respawning" before any yield,
        -- so the death watchdog never mistakes this for a real death.
        local how = doReset()
        log("reset via " .. tostring(how))
        if how then
            waitRespawn(true)
        else
            _wait(0.5)
        end
        if not running then return false end
    end
    return false
end

--=============================== STEP 2: FARM ===========================
local function bindCooldowns(c)
    local ms = c and c:FindFirstChild("Moveset")
    if not ms then return end
    local secs = { ["Rapid Punches"] = 15, ["Twofold Kick"] = 18, ["Reversal Red"] = 12 }
    for name, cd in pairs(secs) do
        local mv = ms:FindFirstChild(name)
        if mv and not watched[mv] then
            watched[mv] = true
            pcall(function()
                mv:GetAttributeChangedSignal("ReadyAt"):Connect(function()
                    cooldowns[name] = true
                    _delay(cd, function() cooldowns[name] = false end)
                end)
            end)
        end
    end
end

local function dummyFree(d)
    local info = d and d:FindFirstChild("Info")
    if not info then return false end
    local k = info:GetChildren()
    return #k == 1 and k[1].Name == "Cancel"
end

local function nobodyNear(d, me, droot)
    local cs = workspace:FindFirstChild("Characters")
    if not cs then return false end
    local k = cs:GetChildren()
    for i = 1, #k do
        local m = k[i]
        if m:IsA("Model") and m ~= me and m ~= d then
            local r = m:FindFirstChild("HumanoidRootPart")
            if r and (r.Position - droot.Position).Magnitude <= NEARBY then return false end
        end
    end
    return true
end

local function firstReadyMove()
    local now = os.clock()
    for i = 1, #KIDNAP_ORDER do
        local n = KIDNAP_ORDER[i]
        if not cooldowns[n] and now - (lastFired[n] or 0) > REFIRE then return n end
    end
    return nil
end

local function kidnap(d, c, root, hum, droot)
    if not dummyFree(d) then say("Waiting for dummy to be free..."); return false end
    if not nobodyNear(d, c, droot) then say("Waiting: someone is near the dummy..."); return false end
    local moveName = firstReadyMove()
    if not moveName then say("Waiting for kidnap move cooldown..."); return false end

    say("Kidnapping Dummy with " .. moveName .. "...")
    local oldRot = hum.AutoRotate
    local conn
    local ok, err = pcall(function()
        hum.AutoRotate = false
        conn = RunS.Heartbeat:Connect(function()
            if not root.Parent or not droot.Parent then
                if conn then conn:Disconnect(); conn = nil end
                return
            end
            root.CFrame = CFrame.new(root.Position,
                Vector3.new(droot.Position.X, root.Position.Y, droot.Position.Z))
        end)
        _delay(1, function()
            if conn then pcall(function() conn:Disconnect() end); conn = nil end
            if hum and hum.Parent then pcall(function() hum.AutoRotate = oldRot end) end
        end)
        if tryMove(c, moveName) then lastFired[moveName] = os.clock() end
        _wait(0.3)
        if not running or not root.Parent or not droot.Parent then return end
        root.CFrame = droot.CFrame * DUMMY_OFF
        _wait(0.4)
        if not cooldowns["Reversal Red"] then
            if tryMove(c, "Reversal Red") then
                lastFired["Reversal Red"] = os.clock()
            end
        end
        if not running or not root.Parent then return end
        root.CFrame = KIDNAP_RETURN_CF
        _wait(4)
    end)
    if conn then pcall(function() conn:Disconnect() end); conn = nil end
    if hum and hum.Parent then pcall(function() hum.AutoRotate = oldRot end) end
    if not ok then say("Kidnap failed: " .. tostring(err)); _wait(0.5); return false end
    return true
end

local function lightAttack(c)
    fire("GojoService", "Activated", "Up", nil)
end

local function attack(c, noDash)
    if not c then return end
    local now = os.clock()

    -- Farm loops run frequently; rate-limit the filler and use the same
    -- cooldown/refire guards as Player mode instead of spamming every remote.
    if now - lastLight >= M1_RATE then
        lightAttack(c)
        lastLight = now
    end
    for i = 1, #KIDNAP_ORDER do
        local moveName = KIDNAP_ORDER[i]
        if not cooldowns[moveName] and now - (lastFired[moveName] or 0) >= REFIRE then
            if tryMove(c, moveName) then lastFired[moveName] = now end
        end
    end

    -- Dashing while farming often moves the character away from the dummy.
    if not noDash then fire("MovementService", "Dash", "Back", true) end
end

-- [v6] regen bail
local function bailAndRegen()
    stopStick()
    say(("HP %.0f%% critical - bailing to regen"):format(hpPct()))
    local r = getHRP()
    if r then pcall(function() r.CFrame = SAFE_CF end) end
    _wait(0.25)
    local t0 = os.clock()
    while active() do
        local c = getChar()
        local h = c and c:FindFirstChildOfClass("Humanoid")
        if not h or h.Health <= 0 then break end
        if hpPct(h) >= cfg.RecoverHP or os.clock() - t0 > 12 then break end
        _wait(0.15)
    end
    say("Recovered - re-engaging")
    if cfg.KidnapTarget then blacklist[cfg.KidnapTarget] = os.clock() + 2 end
end

-- [v6] player mode tick: guard -> resolve -> rotate-on-death -> latch + burst
local function playerKidnapTick(c, root, hum)
    local hp = hpPct(hum)

    -- ---------- HEALTH GUARD ----------
    if cfg.Guard ~= "Off" and hp <= cfg.MinHealth then
        local tname = cfg.KidnapTarget
        if cfg.Guard == "Bail" or hp <= cfg.MinHealth * 0.6 then
            bailAndRegen()
        else
            if tname then blacklist[tname] = os.clock() + 5 end
            if not rotateTarget("low HP", tname) then bailAndRegen() end
        end
        return
    end

    local tgt, tname = resolveTarget()

    -- ---------- NO TARGET: recover stale selection before dummy fallback ----------
    if not tgt then
        local replacement = (cfg.KidnapMode == "Player" and nextTarget(tname)) or nil
        if replacement then
            cfg.KidnapTarget = replacement
            if refreshUI then refreshUI() end
            if saveCfg then saveCfg() end
            stopStick()
            say("Target unavailable - switching to " .. replacement)
            _wait(0.05)
            return
        end

        local d = getDummy()
        local droot = d and d:FindFirstChild("HumanoidRootPart")
        if droot and cfg.FallbackDummy then
            stopStick()
            say("No live players - farming Dummy meanwhile")
            pcall(function() root.CFrame = droot.CFrame * DUMMY_OFF end)
            attack(c, true)
            _wait(FARM_TICK)
        else
            stopStick()
            say("No valid target - waiting...")
            _wait(0.25)
        end
        return
    end

    local troot = tgt:FindFirstChild("HumanoidRootPart")
    local thum = tgt:FindFirstChildOfClass("Humanoid")

    -- ---------- TARGET DIED: instant rotate, never wait for respawn ----------
    if not troot or not thum or thum.Health <= 0 then
        blacklist[tname] = os.clock() + 1.5
        dmgState.target = nil
        if not rotateTarget("target died", tname) then
            say("Everyone is down - holding")
            _wait(0.1)
        end
        return   -- no _wait: next iteration resolves the new target immediately
    end

    -- ---------- TARGET IN DOMAIN ----------
    if cfg.AvoidDomains and inDomain(tgt) then
        blacklist[tname] = os.clock() + 4
        if not rotateTarget("in Domain", tname) then
            stopStick()
            say("Target is in a Domain; no alternate target available")
            _wait(0.15)
        end
        return
    end

    -- ---------- TARGET ULT READY: pre-rotate off the incoming Domain ----------
    local tplr = Players:FindFirstChild(tname)
    if cfg.AvoidDomains and tplr and (tonumber(tplr:GetAttribute("Ultimate")) or 0) >= 100
        and hpPct(thum) > BURST_HP then
        blacklist[tname] = os.clock() + 6
        if not rotateTarget("target ult ready", tname) then
            stopStick()
            say("Target Ultimate ready; no alternate target available")
            _wait(0.15)
        end
        return
    end

    -- ---------- DAMAGE WATCH ----------
    if dmgState.target ~= tname then
        dmgState.target = tname
        dmgState.health = hum.Health
        dmgState.hits = {}
    end
    if dmgState.health and hum.Health < dmgState.health - 0.01 then
        local now = os.clock()
        local keep = { now }
        for i = 1, #dmgState.hits do
            if now - dmgState.hits[i] <= DMG_WINDOW then keep[#keep + 1] = dmgState.hits[i] end
        end
        dmgState.hits = keep
        if #keep >= DMG_LIMIT then
            say("Taking repeated damage - switching target...")
            blacklist[tname] = now + 6
            dmgState.hits = {}
            dmgState.target = nil
            if not rotateTarget("taking damage", tname) then bailAndRegen() end
            return
        end
    end
    dmgState.health = hum.Health

    -- ---------- LATCH BEHIND + MAX PRESSURE ----------
    stickSelf, stickTarget = root, troot
    hum.AutoRotate = false
    snapBehind(root, troot) -- first placement immediately; Heartbeat maintains it

    local now = os.clock()
    local fired = false
    for i = 1, #KIDNAP_ORDER do
        local mv = KIDNAP_ORDER[i]
        if not cooldowns[mv] and now - (lastFired[mv] or 0) > REFIRE then
            if tryMove(c, mv) then
                lastFired[mv] = now
                fired = true
            end
        end
    end
    if now - lastLight >= M1_RATE then
        lightAttack(c)
        lastLight = now
    end
    if fired then
        say(("Kidnap %s | HP %d%%"):format(tname, math.floor(hp)))
    end

    _wait(STICK_TICK)
end

local function farmRoutine()
    local lastUlt, lastGain, lastNag = getUlt(), os.clock(), 0
    local ultHist = {}
    say("Farming Ult")
    while active() do
        local u = getUlt()

        -- ult/sec telemetry
        local now = os.clock()
        ultHist[#ultHist + 1] = { t = now, u = u }
        -- Retain a full window; an item-count cap of 40 is only ~3.2 seconds
        -- at FARM_TICK and made the 5-second rate stay at zero forever.
        while #ultHist > 1 and now - ultHist[1].t > 6 do
            table.remove(ultHist, 1)
        end
        local rate = 0
        for i = 1, #ultHist do
            local elapsed = now - ultHist[i].t
            if elapsed >= 5 then
                rate = (u - ultHist[i].u) / elapsed
                break -- oldest qualifying sample gives the longest useful window
            end
        end
        if ui.ult then
            ui.ult.Text = ("Ultimate: %.0f%% / %d%%  (%.1f/s)  HP %d%%"):format(
                u, ULT_GOAL, rate, math.floor(hpPct()))
        end

        if u >= ULT_GOAL then stopStick(); say("Maxed Ult"); return "completed" end

        if u > lastUlt then
            lastUlt, lastGain = u, now
        elseif now - lastGain >= STALL_LIMIT and now - lastNag >= 8 then
            lastNag = now
            if cfg.KidnapMode == "Player" and rotateTarget("no meter gain", cfg.KidnapTarget) then
                say("No meter gain - rotating target...")
                lastGain = now
            else
                say("No meter gain - restarting from bypass...")
                stopStick()
                return "restart"
            end
        end

        local c = getChar()
        local root = getHRP(c)
        local hum = c and c:FindFirstChildOfClass("Humanoid")

        -- [FIX] re-resolve services on demand instead of bailing out. A cycle
        -- that never touched a remote used to leave Services nil here, which
        -- made farmRoutine abort instantly and look like a restart loop.
        if not Services or not Services.Parent then refreshServices() end

        if not Services then
            say("Knit Services not found")
            stopStick()
            _wait(0.5)
        elseif not c or not root or not hum or hum.Health <= 0 then
            say("Waiting for your character...")
            stopStick()
            _wait(0.5)
        elseif cfg.KidnapMode == "Player" then
            bindCooldowns(c)
            playerKidnapTick(c, root, hum)
        else
            local d = getDummy()
            local droot = d and d:FindFirstChild("HumanoidRootPart")
            if not d or not droot then
                say("Waiting for workspace.Characters.Dummy...")
                stopStick()
                _wait(0.5)
            else
                bindCooldowns(c)
                if cfg.KidnapMode == "Dummy" and (root.Position - droot.Position).Magnitude > CLOSE_DIST then
                    if not kidnap(d, c, root, hum, droot) then _wait(0.25) end
                else
                    say(("Farming Dummy - %.0f%%"):format(u))
                    pcall(function() root.CFrame = droot.CFrame * DUMMY_OFF end)
                    attack(c, true)
                    _wait(FARM_TICK)
                end
            end
        end
    end
    stopStick()
    return "stopped"
end

--=============================== STEP 3: POP & KILL =====================
-- Teleport verification for the pre-ultimate position. The client can be
-- interrupted by stun/knockback, so don't continue merely because PivotTo ran.
local POP_TELEPORT_TOLERANCE = 8       -- studs from TARGET_POS
local POP_TELEPORT_ATTEMPTS = 3
local POP_TELEPORT_VERIFY_TIMEOUT = 1.5
local POP_STABLE_SECONDS = 0.55
local POP_STUN_TIMEOUT = 12

local function waitStun(timeout)
    local deadline = os.clock() + (timeout or POP_STUN_TIMEOUT)
    local clearSince = nil
    local lastMessage = nil

    while active() and os.clock() < deadline do
        local c = getChar()
        local info = c and getInfo(c)
        local message

        if not c or not info then
            clearSince = nil
            message = "Waiting for character state..."
        elseif info:FindFirstChild("Stun") then
            clearSince = nil
            message = "Waiting for stun to end..."
        else
            if not clearSince then clearSince = os.clock() end
            if os.clock() - clearSince >= POP_STABLE_SECONDS then
                return true
            end
        end

        -- Avoid printing the same status every polling tick.
        if message and message ~= lastMessage then
            say(message)
            lastMessage = message
        end
        _wait(0.05)
    end

    if active() then
        say("Stun/character state did not clear; Ultimate cancelled")
    end
    return false
end

local function teleportAndVerify()
    for attempt = 1, POP_TELEPORT_ATTEMPTS do
        if not active() then return false end
        if not waitStun(POP_STUN_TIMEOUT) then return false end

        local c = getChar()
        local root = getHRP(c)
        local hum = c and c:FindFirstChildOfClass("Humanoid")
        if not c or not root or not hum or hum.Health <= 0 then
            say("Teleport check: character/root unavailable")
            _wait(0.15)
        else
            say(("Teleporting to ult position (%d/%d)..."):format(attempt, POP_TELEPORT_ATTEMPTS))
            local moved, moveErr = pcall(function()
                c:PivotTo(TARGET_CF)
            end)

            if not moved then
                log("PivotTo failed: " .. tostring(moveErr))
            else
                local deadline = os.clock() + POP_TELEPORT_VERIFY_TIMEOUT
                local stableSince = nil
                local reportedStun = false
                while active() and os.clock() < deadline do
                    -- Reacquire after each wait because Character may be replaced.
                    local liveChar = getChar()
                    local liveRoot = getHRP(liveChar)
                    local liveHum = liveChar and liveChar:FindFirstChildOfClass("Humanoid")
                    local info = liveChar and getInfo(liveChar)
                    local stunned = (not info) or info:FindFirstChild("Stun") ~= nil
                    local alive = liveHum and liveHum.Health > 0
                    local distance = liveRoot and (liveRoot.Position - TARGET_POS).Magnitude or math.huge

                    if alive and not stunned and distance <= POP_TELEPORT_TOLERANCE then
                        if not stableSince then stableSince = os.clock() end
                        if os.clock() - stableSince >= POP_STABLE_SECONDS then
                            say(("Teleport confirmed (%.1f studs from target)"):format(distance))
                            return true
                        end
                    else
                        stableSince = nil
                        if stunned and not reportedStun then
                            -- A hit during the verification window invalidates the attempt.
                            say("Hit/stun during teleport; rechecking before Ultimate...")
                            reportedStun = true
                        end
                    end
                    _wait(0.05)
                end
            end
        end

        if attempt < POP_TELEPORT_ATTEMPTS and active() then
            say("Teleport not confirmed; retrying after stun check...")
            _wait(0.15)
        end
    end

    if active() then
        say("Teleport verification failed; Ultimate skipped")
    end
    return false
end

local function waitInSkill(timeout)
    local t0 = os.clock()
    repeat
        local i = getInfo()
        if i and i:FindFirstChild("InSkill") then return true end
        _wait(0.05)
    until os.clock() - t0 > (timeout or 5) or not active()
    return false
end

local function killAll()
    local i = getInfo()
    if not i or not i:FindFirstChild("InSkill") then
        say("InSkill not active - skipping kill")
        return
    end
    say("Killing all players")
    local idx = 1
    while active() do
        local i2 = getInfo()
        if not i2 or not i2:FindFirstChild("InSkill") then break end
        local myHRP = getHRP()
        local me = getChar()
        local cs = workspace:FindFirstChild("Characters")
        if myHRP and cs then
            local targets = {}
            local k = cs:GetChildren()
            for n = 1, #k do
                local m = k[n]
                if m:IsA("Model") and m ~= me then
                    local hrp = m:FindFirstChild("HumanoidRootPart")
                    local hum = m:FindFirstChildOfClass("Humanoid")
                    if hrp and hum and hum.Health > 0 then targets[#targets + 1] = hrp end
                end
            end
            if #targets > 0 then
                if idx > #targets then idx = 1 end
                myHRP.CFrame = targets[idx].CFrame * KILL_OFF
                idx = idx + 1
            end
        end
        _wait(0.01)
    end
    say("InSkill ended - stopping teleport")
end

-- [AFK] returns true only when the whole stage genuinely completed, so a
--       stun/teleport/event failure is never counted as a finished cycle.
local function popUltKill()
    stopStick()

    -- First pass: wait for stun to clear and confirm the requested position.
    if not waitStun(POP_STUN_TIMEOUT) then return false end
    if not teleportAndVerify() then return false end

    say("Anti Bug Delay")
    _wait(1)
    if not active() then return false end

    if cfg.WaitForDomains then waitDomains() end
    if not active() then return false end

    -- The delay/domain gate can give an opponent time to interrupt us.
    -- Re-check stun and position immediately before sending the Ultimate event.
    if not waitStun(POP_STUN_TIMEOUT) then return false end
    if not teleportAndVerify() then return false end
    if not active() then return false end

    say("Activating 0.2 Domain")
    if not fire("GojoService", "Ultimate") then
        say("Ultimate event missing/failed; cancelling activation")
        return false
    end
    _wait(0.3)
    if not active() then return false end
    if not fire("GojoService", "RightActivated", nil) then
        say("RightActivated event missing/failed")
        return false
    end
    _wait(4.5)
    if not active() then return false end

    if not waitInSkill(5) then
        say("InSkill never started - activation treated as failed")
        return false
    end
    killAll()
    _wait(1)
    if not active() then return false end

    if cfg.AutoEndAction then
        if cfg.EndMode == "Leave" then
            say("Leaving game...")
            _wait(1)
            leftServer = true
            pcall(function() LP:Kick("Done!") end)
        else
            say("Preparing to Hop Server...")
            _wait(1)
            leftServer = true
            fire("RankedService", "Teleport", 2)
        end
    else
        say("Task finished.")
    end
    return true
end

--=============================== AFK LOOP PLUMBING ======================
-- Reset only cycle-scoped state so a fresh cycle never inherits the last one.
local function resetCycleState()
    stopStick()
    attempts = 0
    if ui.attempts then ui.attempts.Text = "Bypass Attempts: 0" end
    dmgState.target, dmgState.health, dmgState.hits = nil, nil, {}
    lastFired, lastLight, lastRotate = {}, 0, 0
    blacklist = {}
end

-- Re-acquire the live world (survives Leave/Hop) and rebuild the GUI if the
-- place reloaded under us. Keeps a single stick connection - no accumulation.
local function ensureGui()
    if ui.gui and ui.gui.Parent then return end
    local ok = pcall(buildGui)
    if ok and ui.start then
        ui.start.MouseButton1Click:Connect(startWorker)
        paintToggles(); refreshUI()
    end
end

local function refreshWorld()
    Players = game:GetService("Players")
    RS      = game:GetService("ReplicatedStorage")
    RunS    = game:GetService("RunService")
    UIS     = game:GetService("UserInputService")
    LP      = Players.LocalPlayer
    resetRemote = nil
    Services = nil
    -- [FIX] re-resolve immediately. Leaving Services nil here meant a cycle
    -- that never fired a remote (bypass succeeds first try) reached
    -- farmRoutine with Services == nil and bailed in ~0ms.
    refreshServices()
    if stickConn then pcall(function() stickConn:Disconnect() end) end
    stickConn = RunS.Heartbeat:Connect(stickHandler)
    ensureGui()
end

--=============================== CYCLE / WORKER =========================
-- One full pass, in row order, honouring only the enabled rows.
--   "completed" -> the whole sequence finished cleanly
--   "aborted"   -> the character DIED (watchdog flagged it)
--   "fail"      -> a stage genuinely failed (stun/teleport/event)
--   "restart"   -> farm stall, start over from the first enabled row
--   "stopped"   -> STOP was pressed
local function runCycle()
    refreshWorld()

    -- Never start a stage without a fully-loaded, alive, standing character.
    if not stageReady() then
        if not waitRespawn(false) then return "stopped" end
    end

    if cfg.AutoBypass then
        local ok = bypassRoutine()
        if not running then return "stopped" end
        if cycleAbort then return "aborted" end
        if not ok then return "fail" end
        _wait(1)
        if cycleAbort then return "aborted" end
    end

    if cfg.AutoFarm then
        local res = farmRoutine()
        if not running then return "stopped" end
        if cycleAbort then return "aborted" end
        if res == "restart" then return "restart" end
        if res ~= "completed" then return "fail" end
    end

    if cfg.AutoPopUlt then
        local ok = popUltKill()
        if not running then return "stopped" end
        if cycleAbort then return "aborted" end
        if not ok then return "fail" end
    else
        say("Task finished.")
    end

    return "completed"
end

local function worker()
    local lastCycleStart = 0
    while running do
        -- anti-spin: never restart faster than MIN_CYCLE_GAP
        if lastCycleStart > 0 then
            local gap = MIN_CYCLE_GAP - (os.clock() - lastCycleStart)
            if gap > 0 then _wait(gap) end
        end
        lastCycleStart = os.clock()

        -- A death may have been flagged between cycles: wait it out first.
        if cycleAbort or not characterAlive() then
            if not waitRespawn(true) then break end
            resetCycleState()
        end
        cycleAbort = false

        local status = runCycle()
        if not running then break end

        if status == "completed" then
            if not cfg.AFKLoop then say("Sequence finished."); break end
            say("Cycle complete - restarting from row 1 (AFK Loop)")
            resetCycleState()
            _wait(1)

        elseif status == "aborted" then
            -- Real death: wait for a FULL respawn, then restart at row 1.
            if not cfg.AFKLoop then break end
            if not waitRespawn(true) then break end
            cycleAbort = false
            resetCycleState()
            say("Restarting from row 1 (AFK Loop)")

        elseif status == "fail" then
            -- Genuine stage failure: short delay, restart at row 1.
            if not cfg.AFKLoop then break end
            if not characterAlive() then
                if not waitRespawn(true) then break end
            end
            cycleAbort = false
            say("Stage failed - restarting from row 1 (AFK Loop)")
            resetCycleState()
            _wait(1)

        elseif status == "restart" then
            -- Stall restart (original behaviour, independent of AFK Loop).
            cycleAbort = false
            resetCycleState()
            _wait(0.5)

        else -- "stopped"
            break
        end
    end
    stopStick()
end

--=============================== DIAGNOSTICS ============================
local function diag()
    print("======== EZ02 DIAG ========")
    print("target:", tostring(TARGET_POS))
    local s = getSvcFolder()
    print("Services:", s and s:GetFullName() or "NOT FOUND")
    if s then
        local k = s:GetChildren()
        for i = 1, #k do
            local re = k[i]:FindFirstChild("RE")
            local names = {}
            if re then
                local r = re:GetChildren()
                for j = 1, #r do table.insert(names, r[j].Name) end
            end
            print("  " .. k[i].Name .. " RE[" .. #names .. "]: " .. table.concat(names, ", "))
        end
    end
    print("Reset remote:", getReset() and "found" or "NOT FOUND")
    print("ult:", getUlt(), "hp%:", math.floor(hpPct()),
        "ragdoll:", isRagdoll() and "yes" or "no")
    print("kidnap mode:", cfg.KidnapMode, "target:", tostring(cfg.KidnapTarget))
    print("guard:", cfg.Guard, cfg.MinHealth .. "%")
    print("afk loop:", cfg.AFKLoop and "ON" or "off")
    print("valid targets:", table.concat(validTargets(), ", "))
    print("gui:", ui.gui and ui.gui:GetFullName() or "none")
    print("===========================")
end

startWorker = function()
    if running then
        running = false
        stopStick()
        say("Stopped by user")
        refreshUI(); saveCfg()
        return
    end
    if not refreshServices() then say("Knit Services not found"); return end
    running, attempts = true, 0
    cycleAbort, respawning, leftServer = false, false, false
    if ui.attempts then ui.attempts.Text = "Bypass Attempts: 0" end
    refreshUI(); saveCfg()
    say(cfg.AFKLoop and "Starting (AFK Loop)..." or "Starting...")
    diag()

    -- Death watchdog. Exactly one per START; it never spawns workers itself,
    -- it only flips cycleAbort so the single worker restarts cleanly.
    _spawn(function()
        local wasAlive = false
        while running do
            local alive = characterAlive()
            if alive then
                wasAlive = true
            elseif wasAlive and cfg.AFKLoop and not respawning and not cycleAbort then
                cycleAbort = true
                stopStick()
                say("Character died - will restart the cycle")
            end
            _wait(0.1)
        end
    end)

    _spawn(function()
        local ok, err = pcall(worker)
        if not ok then say("Error: " .. tostring(err)) end
        running = false
        stopStick()
        refreshUI(); saveCfg()
    end)
end

--=============================== BOOT ===================================
loadCfg()
if guiOk and ui.start then
    ui.start.MouseButton1Click:Connect(startWorker)
    paintToggles()
    refreshUI()
    say("Ready - press START")
end

stage("3/4 functions ok")

GENV.EZ02_TOKEN = TOKEN
GENV.EZ02_GUI   = ui.gui
GENV.EZ02_Start = startWorker
GENV.EZ02_Diag  = diag
GENV.EZ02_Show  = function()
    if ui.gui then
        ui.gui.Enabled = true
        ui.gui.Parent = LP:WaitForChild("PlayerGui")
    end
end
GENV.EZ02_Stop  = function()
    running = false
    stopStick()
    say("Stopped")
    refreshUI()
end

task.spawn(function()
    while true do
        _wait(1)
        if GENV.EZ02_TOKEN ~= TOKEN then return end
        if ui.gui and not ui.gui.Parent then
            pcall(function() ui.gui.Parent = LP:WaitForChild("PlayerGui", 3) end)
        end
    end
end)

stage("4/4 ready")
print("[Xector Kill farm] done. window: " .. (ui.gui and "yes" or "NO"))