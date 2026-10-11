-- FADeepProbe cursor watch
-- Hooks uimain.lua instead of cursor.lua: userInit.lua imports cursor.lua before UI mods are active,
-- while SetupUI runs afterwards and creates the cursor every time the UI Lua state starts.
-- The pcall swallows the error; FADeepProbe reads the request from the C++ exception FA throws for it.
do
    local oldSetupUI = SetupUI
    function SetupUI()
        oldSetupUI()
        local address = string.gsub(tostring(GetCursor()), "^table: ", "")
        pcall(error, "FADeepProbe watch " .. address .. " _hotspotX _hotspotY", 0)
    end
end
