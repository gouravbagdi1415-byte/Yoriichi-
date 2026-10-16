--============================================================================
--  EZ 0.2  ·  COMBINED
--    [1] Auto Bypass  ->  [2] Auto Farm Dummy  ->  [3] Auto Ult & Kill
--
--  Draggable UI (Auto Bypass style) with 3 toggle rows + START/STOP.
--  Each routine is ported 1:1 from the supplied builds:
--    - Auto Bypass.txt      (closure 445 / 62 / 358->212 / 411 / 76)
--    - Auto Farm Dummy.txt  (kidnap + ultimate farm loop)
--    - Auto Ult & Kill.txt  (teleport -> 0.2 domain -> kill all)
--
--  START runs the toggled stages in order, once. Press STOP anytime.
--============================================================================

local Players           = game:GetService("Players")
local ReplicatedStorage = game:GetService("ReplicatedStorage")
local UserInputService  = game:GetService("UserInputService")
local RunService        = game:GetService("RunService")
local LocalPlayer       = Players.LocalPlayer

local DEBUG = true        -- false = silence the F9 console

-- Values taken verbatim from the original scripts.
local SPOT         = Vector3.new(-57.3561363, 22.9888306, 488.23172)
local SPOT_CFRAME  = CFrame.new(SPOT)
local MAX_DIST     = 20

local KIDNAP_RETURN_CFRAME = CFrame.new(
    -147.833298, -30.7250881, -227.811417,
     0.970708251, -2.46936587e-08, 0.240261301,
    -2.45447391e-12, 1, 1.02788263e-07,
    -0.240261301, -9.97780063e-08, 0.970708251
)
local DUMMY_OFFSET = CFrame.new(0, 0, 2)
local KILL_OFFSET  = CFrame.new(0, 0, 3)

local TARGET_NAME     = "Dummy"
local ULTIMATE_GOAL   = 100
local FARM_INTERVAL   = 0.08
local CLOSE_DISTANCE  = 25
local AUTO_KIDNAP     = true
local NEARBY_CHARACTER_DISTANCE = 15

-- state --------------------------------------------------------------------
local running  = false
local attempts = 0
local toggles  = { bypass = true, farm = true, kill = true }

local statusLabel, attemptsLabel, ultimateLabel, debugLabel
local startButton

local cooldownFlags = { ["Rapid Punches"] = false, ["Twofold Kick"] = false }
local watchedMoves  = setmetatable({}, { __mode = "k" })

--===========================================================================
--  STATUS
--===========================================================================

local function setStatus(msg)
    if statusLabel then
        pcall(function() statusLabel.Text = "Status: " .. tostring(msg) end)
    end
    if DEBUG then print("[EZ02] " .. tostring(msg)) end
end

--===========================================================================
--  SERVICES / REMOTES
--===========================================================================

local services

local function getServices()
    if services and services.Parent then return services end

    local outer = ReplicatedStorage:FindFirstChild("Knit")
    if outer then
        local inner = outer:FindFirstChild("Knit")
        local s = (inner and inner:FindFirstChild("Services")) or outer:FindFirstChild("Services")
        if s then services = s return s end
    end
    for _, d in ipairs(ReplicatedStorage:GetDescendants()) do
        if d.Name == "Services" then services = d return d end
    end
    return nil
end

local function fireRemote(serviceName, remoteName, ...)
    local svc = getServices()
    if not svc then return false end
    local service = svc:FindFirstChild(serviceName)
    local re      = service and service:FindFirstChild("RE")
    local remote  = re and re:FindFirstChild(remoteName)
    if not remote or not remote:IsA("RemoteEvent") then return false end

    local args = { n = select("#", ...), ... }
    local unpackArgs = table.unpack or unpack
    local ok = pcall(function()
        remote:FireServer(unpackArgs(args, 1, args.n))
    end)
    return ok
end

local function gojoRemote(name)
    local svc = getServices()
    local g   = svc and svc:FindFirstChild("GojoService")
    local re  = g and g:FindFirstChild("RE")
    return re and re:FindFirstChild(name)
end

local function getResetRemote()
    local svc = getServices()
    if svc then
        local j = svc:FindFirstChild("JoinService")
        local re = j and j:FindFirstChild("RE")
        local r = re and re:FindFirstChild("Reset")
        if r then return r end
    end
    for _, d in ipairs(ReplicatedStorage:GetDescendants()) do
        if d.Name == "Reset" and d:IsA("RemoteEvent")
            and d.Parent and d.Parent.Name == "RE" then
            return d
        end
    end
    return nil
end

--===========================================================================
--  CHARACTER HELPERS
--===========================================================================

local function getCharacter()
    local char = LocalPlayer.Character
    if not char or not char.Parent then
        local chars = workspace:FindFirstChild("Characters")
        if chars then char = chars:FindFirstChild(LocalPlayer.Name) end
    end
    return char
end

local function getHRP(char)
    char = char or getCharacter()
    return char and char:FindFirstChild("HumanoidRootPart")
end

local function getInfo()
    local c = getCharacter()
    return c and c:FindFirstChild("Info")
end

local function getUltimate()
    return tonumber(LocalPlayer:GetAttribute("Ultimate")) or 0
end

local function getDummy()
    local chars = workspace:FindFirstChild("Characters")
    return chars and chars:FindFirstChild(TARGET_NAME) or nil
end

--===========================================================================
--  STAGE 1 : AUTO BYPASS  (closure 445 / 62 / 358->212 / 411 / 76)
--===========================================================================

local function resetCharacter()
    local remote = getResetRemote()
    if remote then
        pcall(function() remote:FireServer() end)
        return "remote"
    end
    local char = getCharacter()
    local hum  = char and char:FindFirstChildOfClass("Humanoid")
    if hum then
        pcall(function() hum.Health = 0 end)
        return "humanoid"
    end
    return nil
end

local function respawnWait()
    setStatus("Waiting for respawn...")
    task.wait(0.5)
    while running do
        local char = getCharacter()
        if char
            and char:FindFirstChild("HumanoidRootPart")
            and not char:FindFirstChild("RagdollConstraints") then
            local hum = char:FindFirstChildOfClass("Humanoid")
            if hum and hum.Health > 0 then
                if running then
                    setStatus("Respawn complete.")
                    task.wait(0.1)
                end
                return
            end
        end
        task.wait(0.1)
    end
end

local function bypassCycles()
    for cycle = 1, 3 do
        if not running then return false end

        local char = getCharacter()
        local hrp  = getHRP(char)
        if not char or not hrp then
            task.wait(1)
            return false
        end

        setStatus("Bypass Cycle " .. cycle .. "/3...")
        char:PivotTo(SPOT_CFRAME)
        task.wait(0.2)

        hrp = getHRP()
        local dist = hrp and (hrp.Position - SPOT).Magnitude

        if DEBUG then
            print(("[EZ02] cycle %d -> distance %s"):format(
                cycle, dist and string.format("%.1f", dist) or "nil"))
        end
        if dist and debugLabel then
            debugLabel.Text = string.format("cycle %d dist %.1f", cycle, dist)
        end

        if not (hrp and dist and dist <= MAX_DIST) then
            setStatus("Rubberbanded. Resetting...")
            return false
        end

        setStatus("Cycle " .. cycle .. ": OK")
        task.wait(0.1)
    end
    return true
end

local function waitForDomains()
    local domains = workspace:FindFirstChild("Domains")
    if not domains then return end
    while running do
        domains = workspace:FindFirstChild("Domains")
        if not domains or #domains:GetChildren() == 0 then break end
        setStatus("Waiting for Domain to clear...")
        task.wait(0.5)
    end
    if running then
        setStatus("Domain cleared.")
        task.wait(0.2)
    end
end

local function bypassRoutine()
    attempts = 0
    while running do
        attempts += 1
        if attemptsLabel then
            attemptsLabel.Text = "Bypass Attempts: " .. attempts
        end

        if bypassCycles() then
            setStatus("Bypass completed.")
            task.wait(1)
            waitForDomains()
            return true
        end

        local how = resetCharacter()
        if DEBUG then print("[EZ02] reset via " .. tostring(how)) end
        if how then respawnWait() end
    end
    return false
end

--===========================================================================
--  STAGE 2 : AUTO FARM DUMMY
--===========================================================================

local function bindMoveCooldowns(character)
    local moveset = character and character:FindFirstChild("Moveset")
    if not moveset then return end

    local cooldownSeconds = { ["Rapid Punches"] = 15, ["Twofold Kick"] = 18 }
    for moveName, seconds in pairs(cooldownSeconds) do
        local move = moveset:FindFirstChild(moveName)
        if move and not watchedMoves[move] then
            watchedMoves[move] = true
            pcall(function()
                move:GetAttributeChangedSignal("ReadyAt"):Connect(function()
                    cooldownFlags[moveName] = true
                    task.delay(seconds, function()
                        cooldownFlags[moveName] = false
                    end)
                end)
            end)
        end
    end
end

local function chooseKidnapMove()
    if not cooldownFlags["Rapid Punches"] then return "Rapid Punches" end
    if not cooldownFlags["Twofold Kick"] then return "Twofold Kick" end
    return nil
end

local function dummyInfoAllowsKidnap(dummy)
    local info = dummy and dummy:FindFirstChild("Info")
    if not info then return false end
    local children = info:GetChildren()
    return #children == 1 and children[1].Name == "Cancel"
end

local function noOtherCharactersNearDummy(dummy, playerCharacter, dummyRoot)
    local chars = workspace:FindFirstChild("Characters")
    if not chars then return false end
    for _, model in ipairs(chars:GetChildren()) do
        if model:IsA("Model") and model ~= playerCharacter and model ~= dummy then
            local otherRoot = model:FindFirstChild("HumanoidRootPart")
            if otherRoot and (otherRoot.Position - dummyRoot.Position).Magnitude
                <= NEARBY_CHARACTER_DISTANCE then
                return false
            end
        end
    end
    return true
end

local function fireKidnapMove(character, moveName)
    local moveset = character and character:FindFirstChild("Moveset")
    local move = moveset and moveset:FindFirstChild(moveName)
    if not move then return false end
    local serviceName = moveName == "Rapid Punches"
        and "RapidPunchesService" or "TwofoldKickService"
    return fireRemote(serviceName, "Activated", move, nil)
end

local function kidnapDummy(dummy, character, root, humanoid, dummyRoot)
    if not dummyInfoAllowsKidnap(dummy) then
        setStatus("Waiting for dummy to be free...")
        return false
    end
    if not noOtherCharactersNearDummy(dummy, character, dummyRoot) then
        setStatus("Waiting: another character is near the dummy...")
        return false
    end

    local moveName = chooseKidnapMove()
    if not moveName then
        setStatus("Waiting for Rapid Punches / Twofold Kick cooldown...")
        return false
    end

    setStatus("Kidnapping Dummy with " .. moveName .. "...")
    local oldAutoRotate = humanoid.AutoRotate
    local rotateConnection

    local ok, err = pcall(function()
        humanoid.AutoRotate = false
        rotateConnection = RunService.Heartbeat:Connect(function()
            if not root.Parent or not dummyRoot.Parent then
                if rotateConnection then
                    rotateConnection:Disconnect()
                    rotateConnection = nil
                end
                return
            end
            root.CFrame = CFrame.new(
                root.Position,
                Vector3.new(dummyRoot.Position.X, root.Position.Y, dummyRoot.Position.Z)
            )
        end)

        task.delay(1, function()
            if rotateConnection then
                pcall(function() rotateConnection:Disconnect() end)
                rotateConnection = nil
            end
            if humanoid and humanoid.Parent then
                pcall(function() humanoid.AutoRotate = oldAutoRotate end)
            end
        end)

        fireKidnapMove(character, moveName)
        task.wait(0.3)
        if not running or not root.Parent or not dummyRoot.Parent then return end
        root.CFrame = dummyRoot.CFrame * DUMMY_OFFSET
        task.wait(0.4)
        if not running or not root.Parent then return end
        root.CFrame = KIDNAP_RETURN_CFRAME
        task.wait(4)
    end)

    if rotateConnection then
        pcall(function() rotateConnection:Disconnect() end)
        rotateConnection = nil
    end
    if humanoid and humanoid.Parent then
        pcall(function() humanoid.AutoRotate = oldAutoRotate end)
    end

    if not ok then
        setStatus("Kidnap step failed: " .. tostring(err))
        task.wait(0.5)
        return false
    end
    return true
end

local function farmAttackCycle(character)
    local moveset = character and character:FindFirstChild("Moveset")
    if not moveset then
        setStatus("Waiting for Moveset...")
        return
    end

    fireRemote("GojoService", "Activated", "Up", nil)

    local reversalRed = moveset:FindFirstChild("Reversal Red")
    if reversalRed then
        fireRemote("ReversalRedService", "Activated", reversalRed, nil)
    end
    local rapidPunches = moveset:FindFirstChild("Rapid Punches")
    if rapidPunches then
        fireRemote("RapidPunchesService", "Activated", rapidPunches, nil)
    end
    local twofoldKick = moveset:FindFirstChild("Twofold Kick")
    if twofoldKick then
        fireRemote("TwofoldKickService", "Activated", twofoldKick, nil)
    end
    fireRemote("MovementService", "Dash", "Back", true)
end

local function farmStage()
    local lastUltimate  = getUltimate()
    local lastProgressAt = os.clock()
    local lastNoProgressMessage = 0

    setStatus("Farming Ultimate...")

    while running do
        local ultimate = getUltimate()
        if ultimateLabel then
            pcall(function()
                ultimateLabel.Text =
                    string.format("Ultimate: %.0f%% / %d%%", ultimate, ULTIMATE_GOAL)
            end)
        end

        if ultimate >= ULTIMATE_GOAL then
            setStatus("Maxed Ult - 100% reached")
            return
        end

        if ultimate > lastUltimate then
            lastUltimate = ultimate
            lastProgressAt = os.clock()
        elseif os.clock() - lastProgressAt >= 30
            and os.clock() - lastNoProgressMessage >= 10 then
            setStatus("No meter gain yet - checking dummy / remotes...")
            lastNoProgressMessage = os.clock()
        end

        local character = getCharacter()
        local root      = getHRP(character)
        local humanoid  = character and character:FindFirstChildOfClass("Humanoid")
        local dummy     = getDummy()
        local dummyRoot = dummy and dummy:FindFirstChild("HumanoidRootPart")

        if not getServices() then
            setStatus("Knit Services not found in ReplicatedStorage")
            return
        elseif not character or not root or not humanoid or humanoid.Health <= 0 then
            setStatus("Waiting for your character to spawn...")
            task.wait(0.5)
        elseif not dummy or not dummyRoot then
            setStatus("Waiting for workspace.Characters.Dummy...")
            task.wait(0.5)
        else
            bindMoveCooldowns(character)
            local distance = (root.Position - dummyRoot.Position).Magnitude

            if AUTO_KIDNAP and distance > CLOSE_DISTANCE then
                local didKidnap = kidnapDummy(dummy, character, root, humanoid, dummyRoot)
                if not didKidnap then task.wait(0.25) end
            else
                setStatus("Farming Dummy - " .. string.format("%.0f%%", ultimate))
                pcall(function()
                    root.CFrame = dummyRoot.CFrame * DUMMY_OFFSET
                end)
                farmAttackCycle(character)
                task.wait(FARM_INTERVAL)
            end
        end
    end
end

--===========================================================================
--  STAGE 3 : AUTO ULT & KILL
--===========================================================================

local function waitForFullBar()
    while running do
        local ult = getUltimate()
        if ult >= ULTIMATE_GOAL then
            setStatus("Ult full (" .. ult .. ") - popping 0.2...")
            return true
        end
        task.wait(0.1)
    end
    return false
end

local function waitForStunEnd()
    while running do
        local info = getInfo()
        if not info or not info:FindFirstChild("Stun") then return end
        setStatus("Waiting for stun to end...")
        task.wait(0.1)
    end
end

local function waitForDomainsClear()
    local domains = workspace:FindFirstChild("Domains")
    if not domains then return end
    while running and #domains:GetChildren() > 0 do
        setStatus("Waiting for Domain to clear...")
        task.wait(0.5)
    end
end

local function teleportToSpot()
    setStatus("Teleporting to spot...")
    local c = getCharacter()
    if c then c:PivotTo(SPOT_CFRAME) end
end

local function activate02Domain()
    setStatus("Activating 0.2 Domain")
    local ult   = gojoRemote("Ultimate")
    local right = gojoRemote("RightActivated")
    if ult then ult:FireServer() end
    task.wait(0.3)
    if right then right:FireServer(nil) end
end

local function waitForInSkill(timeout)
    local t0 = os.clock()
    repeat
        local info = getInfo()
        if info and info:FindFirstChild("InSkill") then return true end
        task.wait(0.05)
    until os.clock() - t0 > (timeout or 5)
    return false
end

local function killAllPlayers()
    local info = getInfo()
    if not info or not info:FindFirstChild("InSkill") then
        setStatus("InSkill not active - skipping kill")
        return
    end

    setStatus("Killing all players")
    local idx = 1

    while running do
        local info2 = getInfo()
        if not info2 or not info2:FindFirstChild("InSkill") then break end

        local myHRP = getHRP()
        local chars = workspace:FindFirstChild("Characters")
        local me    = getCharacter()

        if myHRP and chars then
            local targets = {}
            for _, model in ipairs(chars:GetChildren()) do
                if model:IsA("Model") and model ~= me then
                    local hrp = model:FindFirstChild("HumanoidRootPart")
                    local hum = model:FindFirstChildOfClass("Humanoid")
                    if hrp and hum and hum.Health > 0 then
                        targets[#targets + 1] = hrp
                    end
                end
            end

            if #targets > 0 then
                if idx > #targets then idx = 1 end
                myHRP.CFrame = targets[idx].CFrame * KILL_OFFSET
                idx += 1
            end
        end

        task.wait(0.01)
    end

    setStatus("InSkill ended - stopping teleport")
end

local function killStage()
    if not waitForFullBar() then return end
    if not running then return end

    waitForStunEnd()
    if not running then return end

    teleportToSpot()
    task.wait(1)                 -- "Anti Bug Delay"
    if not running then return end

    waitForDomainsClear()
    if not running then return end

    activate02Domain()
    task.wait(4.5)

    if running and waitForInSkill(5) then
        killAllPlayers()
    end
    task.wait(1)
end

--=======================================================================
