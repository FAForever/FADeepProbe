-- FADeepProbe watch example
-- Asks FADeepProbe to watch memory, so its report names whatever writes there.
-- Copy the function below into your own hook and call it once the memory to watch exists.
-- FADeepProbe watches up to 4 dwords, and each request replaces the previous one.
-- Without FADeepProbe, the requests do nothing.

--- Watches up to 4 addresses, given as hex strings with an optional hex offset, such as "1A2B3C40+B4".
--- Give a structure's address as the base and the field as the offset: the log shows them that way, so it's
--- clear which structure and field each line is about.
--- The first write by each instruction gets a full report: registers, stack, Lua calls and code.
---@param ... string # addresses
local function FADeepProbeWatchAddresses(...)
    pcall(error, "FADeepProbe watchaddr " .. table.concat(arg, " "), 0)
end

-- Example: watch the metatable (+C) and node array (+14) fields of the cursor's Lua table.
-- SetupUI creates the cursor, and runs again with a new cursor each time the UI Lua state starts.
do
    local oldSetupUI = SetupUI
    function SetupUI()
        oldSetupUI()
        local cursor = string.gsub(tostring(GetCursor()), "^table: ", "")
        FADeepProbeWatchAddresses(cursor .. "+C", cursor .. "+14")

        -- Example: watch addresses found in a reproducible crash report. This replaces the watch above.
        -- FADeepProbeWatchAddresses("11502000+474", "11505474")
        --
        -- FADeepProbe's "Watch:" section logs each address by game tick, and gives each new writer a numbered report:
        --     0x11502000+0x474 0 armed
        --     0x11502000+0x474 120 first write by 0x0128E289, 0x00000004 -> 0x00000000, report 1
        --     0x11502000+0x474 0-3779 writes:
        --         12 by ltable.c
        --         4214 by 0x0128E289, last value 0x00000000
        -- A later request adds its own "armed" lines, and the old addresses keep their lines.
    end
end
