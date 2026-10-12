-- FADeepProbe watch example
-- Asks FADeepProbe to watch memory and probe code, so its report names whatever writes the memory or runs
-- the code. Copy the functions below into your own hook.
-- Without FADeepProbe, the requests do nothing.

--- Watches up to 4 addresses, given as hex strings with an optional hex offset, such as "1A2B3C40+B4".
--- Give a structure's address as the base and the field as the offset: the log shows them that way, so it's
--- clear which structure and field each line is about.
--- The first write by each instruction gets a full report: registers, stack, Lua calls and code.
--- Each request replaces all watched addresses, even if it names fewer than 4.
---@param ... string # addresses
local function FADeepProbeWatchAddresses(...)
    pcall(error, "FADeepProbe watchaddr " .. table.concat(arg, " "), 0)
end

--- Probes code addresses, given as hex strings. FADeepProbe counts each probe's hits and collects the C++
--- classes and Lua calls that reach it.
--- Add watch expressions after colons to watch them on the probe's next hit, such as "438310:ecx+474".
--- An expression is a register with an optional offset, or a dword read from one in brackets, such as "[esp+4]+10".
---@param ... string # probes
local function FADeepProbeProbe(...)
    pcall(error, "FADeepProbe probe " .. table.concat(arg, " "), 0)
end

-- Example: watch the metatable (+C) and node array (+14) fields of the cursor's Lua table.
-- SetupUI creates the cursor, and runs again with a new cursor each time the UI Lua state starts.
do
    local oldSetupUI = SetupUI
    function SetupUI()
        oldSetupUI()
        local cursor = string.gsub(tostring(GetCursor()), "^table: ", "")
        FADeepProbeWatchAddresses(cursor .. "+C", cursor .. "+14")

        -- Example: watch addresses found in a reproducible crash report. This replaces both cursor addresses.
        -- FADeepProbeWatchAddresses("11502000+474", "11505474")

        -- Example: probe the CD3DPrimBatcher constructor, and watch +474 of the next batcher it constructs.
        -- Once the probe is hit, this replaces all watched addresses.
        -- FADeepProbeProbe("438310:ecx+474")
        --
        -- FADeepProbe's "Watch:" section logs each address by game tick, and gives each new writer a numbered report:
        --     0x00438310 0 probe armed, watches ecx+474 on the next hit
        --     0x11502000+0x474 12 armed by probe 0x00438310 (ecx+474)
        --     0x11502000+0x474 120 first write by 0x0128E289, 0x00000004 -> 0x00000000, report 1
        --     0x11502000+0x474 12-3779 writes:
        --         0 by ltable.c
        --         4214 by 0x0128E289, last value 0x00000000
        --     0x00438310 12-3779 3 hits
        -- A later request adds its own "armed" lines, and the old addresses keep their lines.
    end
end
