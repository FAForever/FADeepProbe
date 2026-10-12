-- FADeepProbe watch
-- Asks FADeepProbe to watch the addresses where a stray write zeroed a Lua key type tag in earlier crashes
-- of replay 27939676: the cursor's table in two of them, a tree's table in the third.
-- SetupUI runs before the game starts, early enough to catch the write, and every time the UI Lua state starts.
-- The pcall swallows the error; FADeepProbe reads the request from the C++ exception FA throws for it.
do
    local oldSetupUI = SetupUI
    function SetupUI()
        oldSetupUI()
        pcall(error, "FADeepProbe watchaddr 11502474 11503474 11504474 11505474", 0)
    end
end
