--[[
    Invis ID Tester (executor / client-side)
    ----------------------------------------
    * Paste a big list of animation IDs
    * Cycle Prev / Next (or click the list) to swap the active ID
    * Toggle invis with the CURRENT id
    * Freeze-time scrubber (find the exact frame that hides you)
    * ★ mark the IDs that work, copy them out at the end
    * Manual jump is kept (humanoid is detached while ON)
--]]

local Players = game:GetService("Players")
local UIS     = game:GetService("UserInputService")

local player = Players.LocalPlayer
if not player then warn("INVIS: no LocalPlayer"); return end
local playerGui = player:WaitForChild("PlayerGui")

local character = player.Character or player.CharacterAdded:Wait()
local humanoid  = character:WaitForChild("Humanoid")
local rootPart  = character:WaitForChild("HumanoidRootPart")
local camera    = workspace.CurrentCamera

-- ============================================================
-- CONFIG
-- ============================================================
local IDS = {
    "119635500264882",
    -- you can also just paste everything into the GUI box instead
}

local JUMP_POWER = 50

-- ============================================================
-- STATE
-- ============================================================
local currentIndex   = 1
local isOn           = false
local clonedHumanoid = nil
local frozenTrack    = nil
local jumpConnections = {}
local freezeTime     = 0
local workingIds     = {}
local idButtons      = {}

-- forward declarations so the callbacks can see them
local updateStatus, notify, refreshHighlight, updateStarBtn
local rebuildList, selectIndex, enableInvis, disableInvis

local function currentId()
    return IDS[currentIndex]
end

local function isWorking(id)
    if not id then return false end
    for _, v in ipairs(workingIds) do
        if v == id then return true end
    end
    return false
end

-- ============================================================
-- GUI
-- ============================================================
local screenGui = Instance.new("ScreenGui")
screenGui.Name = "InvisIdTester"
screenGui.ResetOnSpawn = false
screenGui.ZIndexBehavior = Enum.ZIndexBehavior.Sibling
screenGui.Parent = playerGui

local frame = Instance.new("Frame")
frame.Size = UDim2.new(0, 340, 0, 540)
frame.Position = UDim2.new(0, 20, 0, 20)
frame.BackgroundColor3 = Color3.fromRGB(30, 30, 34)
frame.BorderSizePixel = 0
frame.Active = true
frame.Parent = screenGui

Instance.new("UICorner", frame).CornerRadius = UDim.new(0, 10)
local fStroke = Instance.new("UIStroke", frame)
fStroke.Color = Color3.fromRGB(70, 70, 80)
fStroke.Thickness = 1

-- header (draggable)
local header = Instance.new("Frame")
header.Size = UDim2.new(1, 0, 0, 30)
header.BackgroundColor3 = Color3.fromRGB(40, 40, 46)
header.BorderSizePixel = 0
header.Parent = frame
Instance.new("UICorner", header).CornerRadius = UDim.new(0, 10)

local title = Instance.new("TextLabel")
title.Size = UDim2.new(1, -12, 1, 0)
title.Position = UDim2.new(0, 12, 0, 0)
title.BackgroundTransparency = 1
title.TextColor3 = Color3.fromRGB(235, 235, 235)
title.Font = Enum.Font.GothamBold
title.TextSize = 14
title.TextXAlignment = Enum.TextXAlignment.Left
title.Text = "Invis ID Tester"
title.Parent = header

-- invis toggle
local toggleBtn = Instance.new("TextButton")
toggleBtn.Size = UDim2.new(1, -24, 0, 44)
toggleBtn.Position = UDim2.new(0, 12, 0, 40)
toggleBtn.BackgroundColor3 = Color3.fromRGB(45, 45, 50)
toggleBtn.TextColor3 = Color3.fromRGB(255, 255, 255)
toggleBtn.Font = Enum.Font.GothamBold
toggleBtn.TextSize = 16
toggleBtn.Text = "Invis: OFF"
toggleBtn.BorderSizePixel = 0
toggleBtn.Parent = frame
Instance.new("UICorner", toggleBtn).CornerRadius = UDim.new(0, 8)

-- status
local statusLabel = Instance.new("TextLabel")
statusLabel.Size = UDim2.new(1, -24, 0, 20)
statusLabel.Position = UDim2.new(0, 12, 0, 88)
statusLabel.BackgroundTransparency = 1
statusLabel.TextColor3 = Color3.fromRGB(200, 200, 210)
statusLabel.Font = Enum.Font.Code
statusLabel.TextSize = 13
statusLabel.TextXAlignment = Enum.TextXAlignment.Left
statusLabel.Text = ""
statusLabel.Parent = frame

local function makeBtn(parent, text)
    local b = Instance.new("TextButton")
    b.BackgroundColor3 = Color3.fromRGB(55, 55, 62)
    b.TextColor3 = Color3.fromRGB(230, 230, 230)
    b.Font = Enum.Font.Gotham
    b.TextSize = 13
    b.Text = text
    b.BorderSizePixel = 0
    b.AutoButtonColor = true
    b.Parent = parent
    Instance.new("UICorner", b).CornerRadius = UDim.new(0, 6)
    return b
end

-- prev / next
local prevBtn = makeBtn(frame, "◀ Prev")
prevBtn.Size = UDim2.new(0.5, -18, 0, 30)
prevBtn.Position = UDim2.new(0, 12, 0, 112)

local nextBtn = makeBtn(frame, "Next ▶")
nextBtn.Size = UDim2.new(0.5, -18, 0, 30)
nextBtn.Position = UDim2.new(0.5, 6, 0, 112)

-- copy / star row
local row3 = Instance.new("Frame")
row3.Size = UDim2.new(1, -24, 0, 28)
row3.Position = UDim2.new(0, 12, 0, 148)
row3.BackgroundTransparency = 1
row3.Parent = frame
local r3l = Instance.new("UIListLayout", row3)
r3l.FillDirection = Enum.FillDirection.Horizontal
r3l.Padding = UDim.new(0, 6)
r3l.SortOrder = Enum.SortOrder.LayoutOrder

local function smallBtn(text, order)
    local b = makeBtn(row3, text)
    b.Size = UDim2.new(0.333, -4, 1, 0)
    b.LayoutOrder = order
    return b
end
local copyIdBtn      = smallBtn("Copy ID", 1)
local starBtn        = smallBtn("★ Mark", 2)
local copyWorkingBtn = smallBtn("Copy ★", 3)

-- freeze time row
local freezeRow = Instance.new("Frame")
freezeRow.Size = UDim2.new(1, -24, 0, 28)
freezeRow.Position = UDim2.new(0, 12, 0, 182)
freezeRow.BackgroundTransparency = 1
freezeRow.Parent = frame

local freezeLabel = Instance.new("TextLabel")
freezeLabel.Size = UDim2.new(0, 110, 1, 0)
freezeLabel.BackgroundTransparency = 1
freezeLabel.TextColor3 = Color3.fromRGB(200, 200, 210)
freezeLabel.Font = Enum.Font.Gotham
freezeLabel.TextSize = 12
freezeLabel.TextXAlignment = Enum.TextXAlignment.Left
freezeLabel.Text = "Freeze t (s):"
freezeLabel.Parent = freezeRow

local freezeBox = Instance.new("TextBox")
freezeBox.Size = UDim2.new(0, 80, 1, 0)
freezeBox.Position = UDim2.new(0, 110, 0, 0)
freezeBox.BackgroundColor3 = Color3.fromRGB(55, 55, 62)
freezeBox.TextColor3 = Color3.fromRGB(230, 230, 230)
freezeBox.Font = Enum.Font.Code
freezeBox.TextSize = 13
freezeBox.Text = "0"
freezeBox.ClearTextOnFocus = false
freezeBox.Parent = freezeRow
Instance.new("UICorner", freezeBox).CornerRadius = UDim.new(0, 6)

local applyFreezeBtn = makeBtn(freezeRow, "Apply")
applyFreezeBtn.Size = UDim2.new(0, 70, 1, 0)
applyFreezeBtn.Position = UDim2.new(1, -70, 0, 0)

-- paste area
local pasteLabel = Instance.new("TextLabel")
pasteLabel.Size = UDim2.new(1, -24, 0, 16)
pasteLabel.Position = UDim2.new(0, 12, 0, 218)
pasteLabel.BackgroundTransparency = 1
pasteLabel.TextColor3 = Color3.fromRGB(190, 190, 200)
pasteLabel.Font = Enum.Font.Gotham
pasteLabel.TextSize = 12
pasteLabel.TextXAlignment = Enum.TextXAlignment.Left
pasteLabel.Text = "Paste IDs (any digits, one per line):"
pasteLabel.Parent = frame

local pasteBox = Instance.new("TextBox")
pasteBox.Size = UDim2.new(1, -24, 0, 84)
pasteBox.Position = UDim2.new(0, 12, 0, 236)
pasteBox.BackgroundColor3 = Color3.fromRGB(20, 20, 24)
pasteBox.TextColor3 = Color3.fromRGB(220, 220, 220)
pasteBox.PlaceholderText = "119635500264882\n..."
pasteBox.PlaceholderColor3 = Color3.fromRGB(120, 120, 130)
pasteBox.Font = Enum.Font.Code
pasteBox.TextSize = 12
pasteBox.MultiLine = true
pasteBox.ClearTextOnFocus = false
pasteBox.TextWrapped = true
pasteBox.TextXAlignment = Enum.TextXAlignment.Left
pasteBox.TextYAlignment = Enum.TextYAlignment.Top
pasteBox.Text = ""
pasteBox.Parent = frame
Instance.new("UICorner", pasteBox).CornerRadius = UDim.new(0, 6)

local loadBtn = makeBtn(frame, "Load IDs")
loadBtn.Size = UDim2.new(1, -24, 0, 28)
loadBtn.Position = UDim2.new(0, 12, 0, 326)

-- list
local listFrame = Instance.new("ScrollingFrame")
listFrame.Size = UDim2.new(1, -24, 0, 150)
listFrame.Position = UDim2.new(0, 12, 0, 362)
listFrame.BackgroundColor3 = Color3.fromRGB(20, 20, 24)
listFrame.BorderSizePixel = 0
listFrame.CanvasSize = UDim2.new(0, 0, 0, 0)
listFrame.AutomaticCanvasSize = Enum.AutomaticSize.Y
listFrame.ScrollBarThickness = 6
listFrame.ScrollBarImageColor3 = Color3.fromRGB(90, 90, 100)
listFrame.Parent = frame
Instance.new("UICorner", listFrame).CornerRadius = UDim.new(0, 6)

local listPad = Instance.new("UIPadding", listFrame)
listPad.PaddingTop = UDim.new(0, 4)
listPad.PaddingBottom = UDim.new(0, 4)
listPad.PaddingLeft = UDim.new(0, 4)
listPad.PaddingRight = UDim.new(0, 4)

local listLayout = Instance.new("UIListLayout", listFrame)
listLayout.SortOrder = Enum.SortOrder.LayoutOrder
listLayout.Padding = UDim.new(0, 4)

-- drag
local dragging, dragStart, startPos = false, nil, nil
header.InputBegan:Connect(function(input)
    if input.UserInputType == Enum.UserInputType.MouseButton1
    or input.UserInputType == Enum.UserInputType.Touch then
        dragging = true
        dragStart = input.Position
        startPos = frame.Position
        input.Changed:Connect(function()
            if input.UserInputState == Enum.UserInputState.End then
                dragging = false
            end
        end)
    end
end)
UIS.InputChanged:Connect(function(input)
    if dragging and (input.UserInputType == Enum.UserInputType.MouseMovement
    or input.UserInputType == Enum.UserInputType.Touch) then
        local d = input.Position - dragStart
        frame.Position = UDim2.new(
            startPos.X.Scale, startPos.X.Offset + d.X,
            startPos.Y.Scale, startPos.Y.Offset + d.Y)
    end
end)

-- ============================================================
-- STATUS / LIST HELPERS
-- ============================================================
local statusToken = 0

updateStatus = function()
    statusToken = statusToken + 1
    local id = currentId() or "(none)"
    local star = isWorking(id) and "  ★" or ""
    statusLabel.Text = string.format("%d / %d   •   %s%s", currentIndex, #IDS, id, star)
end

notify = function(msg)
    statusToken = statusToken + 1
    local tok = statusToken
    statusLabel.Text = msg
    task.delay(1.6, function()
        if statusToken == tok then updateStatus() end
    end)
end

updateStarBtn = function()
    local id = currentId()
    if id and isWorking(id) then
        starBtn.Text = "★ Unmark"
    else
        starBtn.Text = "★ Mark"
    end
end

refreshHighlight = function()
    for i, btn in ipairs(idButtons) do
        local id = IDS[i]
        local working = isWorking(id)
        btn.Text = (working and "★ " or "  ") .. string.format("%d. %s", i, id)
        btn.TextColor3 = working
            and Color3.fromRGB(255, 215, 0)
            or  Color3.fromRGB(220, 220, 220)
        btn.BackgroundColor3 = (i == currentIndex)
            and Color3.fromRGB(0, 120, 60)
            or  Color3.fromRGB(40, 40, 40)
    end
    updateStarBtn()
end

rebuildList = function()
    for _, c in ipairs(listFrame:GetChildren()) do
        if c:IsA("TextButton") then c:Destroy() end
    end
    idButtons = {}
    for i, id in ipairs(IDS) do
        local row = Instance.new("TextButton")
        row.Size = UDim2.new(1, -14, 0, 26)
        row.BackgroundColor3 = Color3.fromRGB(40, 40, 40)
        row.TextColor3 = Color3.fromRGB(220, 220, 220)
        row.Font = Enum.Font.Code
        row.TextSize = 13
        row.Text = string.format("%d. %s", i, id)
        row.TextXAlignment = Enum.TextXAlignment.Left
        row.BorderSizePixel = 0
        row.LayoutOrder = i
        row.Parent = listFrame
        Instance.new("UICorner", row).CornerRadius = UDim.new(0, 4)
        row.MouseButton1Click:Connect(function() selectIndex(i) end)
        idButtons[i] = row
    end
    refreshHighlight()
end

-- ============================================================
-- MANUAL JUMP (humanoid is detached while ON)
-- ============================================================
local function isGrounded()
    if not rootPart or not rootPart.Parent then return false end
    local params = RaycastParams.new()
    params.FilterType = Enum.RaycastFilterType.Exclude
    params.FilterDescendantsInstances = {character}
    local hit = workspace:Raycast(rootPart.Position, Vector3.new(0, -6, 0), params)
    return hit ~= nil
end

local function doJump()
    if not rootPart or not rootPart.Parent then return end
    if not isGrounded() then return end
    local v = rootPart.AssemblyLinearVelocity
    rootPart.AssemblyLinearVelocity = Vector3.new(v.X, JUMP_POWER, v.Z)
end

local function startJumpListening()
    jumpConnections = {}
    table.insert(jumpConnections, UIS.JumpRequest:Connect(doJump))
    table.insert(jumpConnections, UIS.InputBegan:Connect(function(input, gpe)
        if gpe then return end
        if input.KeyCode == Enum.KeyCode.Space then doJump() end
    end))
end

local function stopJumpListening()
    for _, c in ipairs(jumpConnections) do
        pcall(function() c:Disconnect() end)
    end
    jumpConnections = {}
end

-- ============================================================
-- ENABLE / DISABLE
-- ============================================================
local function cleanupPartial()
    if clonedHumanoid then
        pcall(function() clonedHumanoid:Destroy() end)
        clonedHumanoid = nil
    end
    if frozenTrack then
        pcall(function() frozenTrack:Stop(0); frozenTrack:Destroy() end)
        frozenTrack = nil
    end
    if camera and humanoid then camera.CameraSubject = humanoid end
end

enableInvis = function()
    if isOn then return end
    local id = currentId()
    if not id then notify("No ID selected"); return end
    if not character or not character.Parent then return end
    if not humanoid or not humanoid.Parent then return end

    -- 1) fake humanoid for camera / no nameplate
    clonedHumanoid = humanoid:Clone()
    clonedHumanoid.NameDisplayDistance   = 0
    clonedHumanoid.HealthDisplayDistance = 0
    clonedHumanoid.DisplayDistanceType   = Enum.HumanoidDisplayDistanceType.None
    clonedHumanoid.Parent = character
    if camera then camera.CameraSubject = clonedHumanoid end

    -- 2) frozen animation on the ORIGINAL humanoid
    local animator = humanoid:FindFirstChildOfClass("Animator")
    if not animator then
        animator = Instance.new("Animator")
        animator.Parent = humanoid
    end

    local animInstance = Instance.new("Animation")
    animInstance.AnimationId = "rbxassetid://" .. id

    local ok, err = pcall(function()
        frozenTrack = animator:LoadAnimation(animInstance)
        frozenTrack:Play()
        frozenTrack.TimePosition = freezeTime
        frozenTrack:AdjustSpeed(0)
        frozenTrack:AdjustWeight(9999)
    end)
    if not ok then
        warn("INVIS: animation failed -> " .. tostring(err))
        cleanupPartial()
        notify("Anim load failed")
        return
    end

    -- heuristic: an invalid/empty animation has Length ~= 0
    if frozenTrack.Length and frozenTrack.Length <= 0 then
        cleanupPartial()
        notify("Empty animation (invalid ID?)")
        return
    end

    task.wait()

    -- 3) detach original humanoid
    if humanoid and humanoid.Parent and frozenTrack then
        local ok2 = pcall(function() humanoid.Parent = frozenTrack end)
        if not ok2 then
            -- fallback: at least get it out of the character
            pcall(function() humanoid.Parent = nil end)
        end
    end

    startJumpListening()
    isOn = true
    toggleBtn.Text = "Invis: ON"
    toggleBtn.BackgroundColor3 = Color3.fromRGB(0, 140, 60)
    updateStatus()
end

disableInvis = function()
    if not isOn then return end

    stopJumpListening()

    -- reattach FIRST (so it isn't destroyed with the track)
    if humanoid then
        pcall(function() humanoid.Parent = character end)
    end
    if frozenTrack then
        pcall(function() frozenTrack:Stop(0); frozenTrack:Destroy() end)
        frozenTrack = nil
    end
    if clonedHumanoid then
        pcall(function() clonedHumanoid:Destroy() end)
        clonedHumanoid = nil
    end
    if camera and humanoid then camera.CameraSubject = humanoid end

    isOn = false
    toggleBtn.Text = "Invis: OFF"
    toggleBtn.BackgroundColor3 = Color3.fromRGB(45, 45, 50)
    updateStatus()
end

-- ============================================================
-- SELECTION
-- ============================================================
selectIndex = function(i)
    if #IDS == 0 then return end
    if i < 1 or i > #IDS then return end
    local wasOn = isOn
    if wasOn then disableInvis() end
    currentIndex = i
    updateStatus()
    refreshHighlight()
    if wasOn then enableInvis() end
end

local function go(delta)
    if #IDS == 0 then return end
    local i = currentIndex + delta
    if i < 1 then i = #IDS elseif i > #IDS then i = 1 end
    selectIndex(i)
end

-- ============================================================
-- BUTTON HOOKS
-- ============================================================
toggleBtn.MouseButton1Click:Connect(function()
    if isOn then disableInvis() else enableInvis() end
end)
prevBtn.MouseButton1Click:Connect(function() go(-1) end)
nextBtn.MouseButton1Click:Connect(function() go(1) end)

copyIdBtn.MouseButton1Click:Connect(function()
    local id = currentId()
    if not id then return end
    if setclipboard then
        setclipboard(id)
        notify("Copied " .. id)
    else
        print("ID: " .. id)
        notify("Printed ID to console")
    end
end)

starBtn.MouseButton1Click:Connect(function()
    local id = currentId()
    if not id then return end
    if isWorking(id) then
        for i, v in ipairs(workingIds) do
            if v == id then table.remove(workingIds, i) break end
        end
        notify("Unmarked " .. id)
    else
        table.insert(workingIds, id)
        notify("Marked " .. id)
    end
    refreshHighlight()
    updateStatus()
end)

copyWorkingBtn.MouseButton1Click:Connect(function()
    if #workingIds == 0 then notify("No working IDs marked"); return end
    local txt = table.concat(workingIds, "\n")
    if setclipboard then
        setclipboard(txt)
        notify("Copied " .. #workingIds .. " ID(s)")
    else
        print("--- WORKING IDS ---\n" .. txt)
        notify("Printed working IDs to console")
    end
end)

local function parseIds(text)
    local out = {}
    for num in text:gmatch("%d+") do
        if #num >= 5 then table.insert(out, num) end
    end
    return out
end

loadBtn.MouseButton1Click:Connect(function()
    local parsed = parseIds(pasteBox.Text)
    if #parsed == 0 then notify("No IDs found in text"); return end
    if isOn then disableInvis() end
    IDS = parsed
    currentIndex = 1
    rebuildList()
    updateStatus()
    notify("Loaded " .. #IDS .. " IDs")
end)

-- freeze time
local function applyFreeze(silent)
    local n = tonumber(freezeBox.Text)
    if not n or n < 0 then
        if not silent then notify("Bad freeze time") end
        return
    end
    freezeTime = n
    if frozenTrack then
        pcall(function() frozenTrack.TimePosition = freezeTime end)
    end
    if not silent then notify("Freeze t = " .. tostring(freezeTime)) end
end

applyFreezeBtn.MouseButton1Click:Connect(function() applyFreeze(false) end)
freezeBox.FocusLost:Connect(function() applyFreeze(true) end)

-- ============================================================
-- RESPAWN
-- ============================================================
player.CharacterAdded:Connect(function(newChar)
    stopJumpListening()

    if isOn then
        isOn = false
        clonedHumanoid = nil
        frozenTrack = nil
        toggleBtn.Text = "Invis: OFF"
        toggleBtn.BackgroundColor3 = Color3.fromRGB(45, 45, 50)
    end

    character = newChar
    humanoid  = newChar:WaitForChild("Humanoid")
    rootPart  = newChar:WaitForChild("HumanoidRootPart")

    if camera then camera.CameraSubject = humanoid end
    updateStatus()
end)

-- ============================================================
-- INIT
-- ============================================================
rebuildList()
updateStatus()
print("[InvisIdTester] Paste IDs into the box, hit Load, then Prev/Next to test. ★ marks good ones.")