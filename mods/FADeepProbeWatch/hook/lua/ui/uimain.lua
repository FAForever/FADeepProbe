-- FADeepProbe watch example
-- Shows how Lua asks FADeepProbe to watch memory with hardware write breakpoints, so the crash report names
-- whatever writes it. Copy the two functions below into a hook of your own and call them once the memory you
-- want to watch exists.
--
-- A request is a Lua error raised inside pcall: FA throws Lua errors as C++ exceptions, so FADeepProbe reads the
-- request from the exception while the pcall swallows the error. Without FADeepProbe the request does nothing.
-- FADeepProbe watches up to 4 dwords at a time, and each request replaces the previous one.
-- Reports appear in the `Watch:` section of FADeepProbe's report.

--- Asks FADeepProbe to watch the type tags of up to 4 string keys of a table. Only Lua's table code writes them,
--- so any other write is reported. The keys must already be in the table; FADeepProbe finds them again when the
--- table moves to a new node array.
---@param t table
---@param ... string # keys
local function FADeepProbeWatchKeys(t, ...)
    local address = string.gsub(tostring(t), "^table: ", "")
    pcall(error, "FADeepProbe watch " .. address .. " " .. table.concat(arg, " "), 0)
end

--- Asks FADeepProbe to watch up to 4 raw addresses, as hex strings with an optional hex offset such as
--- "1A2B3C40+B4", since Lua numbers are floats and can't hold an address. An address counts as a key type tag of
--- a table once Lua's table code writes it, and any other write while the table keeps that node array is
--- reported. Other writes are counted per instruction.
---@param ... string # addresses
local function FADeepProbeWatchAddresses(...)
    pcall(error, "FADeepProbe watchaddr " .. table.concat(arg, " "), 0)
end

-- Example: watch the cursor's hotspot keys, which a stray write zeroed in crashes of replays 27939676 and 27928517.
-- This hooks uimain.lua instead of cursor.lua because userInit.lua imports cursor.lua before UI mods are active.
-- SetupUI runs afterwards and creates the cursor, and it runs again with a new cursor every time the UI Lua
-- state starts.
do
    local oldSetupUI = SetupUI
    function SetupUI()
        oldSetupUI()
        FADeepProbeWatchKeys(GetCursor(), "_hotspotX", "_hotspotY")

        -- Example: watch addresses from an earlier crash report, here node 9's key type tag (+B4) of the node
        -- arrays that were hit. Addresses only repeat between runs with the same allocations, such as the same
        -- replay. Uncomment to use; it replaces the key watch above.
        -- FADeepProbeWatchAddresses("11502000+474", "11505474")
    end
end
