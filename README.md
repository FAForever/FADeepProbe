# FADeepProbe
- In the case of a crash replaces BugSplat.
- Integrates with the FA log.
- Collects a lot more information.
- Can be placed between the client and the game.
- Protects the game from attaching a debugger.
- Does not affect performance.

### Usage
```
FADeepProbe.exe [exe_path] [/p <hex_address>] [/<game_arg> ...]
```
- **`exe_path`**: Path to game executable.
  - Defaults to `ForgedAlliance.exe` in directory of FADeepProbe or `%ProgramData%\FAForever\bin\ForgedAlliance.exe`
- **`/p <hex_address>`**: Collect data for Lua calls reaching a specific hex address.
- **`/<game_arg> ...`**: Arguments passed to the game.

### Watching memory
Lua code can ask FADeepProbe to watch up to 4 dwords with hardware write breakpoints:
```lua
pcall(error, "FADeepProbe watch " .. string.gsub(tostring(t), "^table: ", "") .. " key1 key2", 0)
pcall(error, "FADeepProbe watchaddr 11502474 11505474", 0)
```
FA throws Lua errors as C++ exceptions, so FADeepProbe sees the request while the pcall swallows it.
- `watch` watches the type tags of string keys of a table. Only Lua's table code writes them, so any other write is reported.
- `watchaddr` watches raw addresses. An address counts as a key type tag of a table once Lua's table code writes it with that table in a register, and any other write while the table keeps that node array is reported. Other writes are counted per instruction.

Reports appear in the `Watch:` section of the report, with the writer's registers, stack, Lua calls and code, and the table.
Key tags that change without a reported write, such as kernel writes, are reported when FADeepProbe polls them.

The `mods/FADeepProbeWatch` UI mod watches the addresses where a stray write has been corrupting Lua tables.

### Building
Requires [Free Pascal](https://www.freepascal.org/) 3.2.2 targeting i386-win32. All other compiler settings are in the source.
```
fpc -O2 FADeepProbe.dpr
```
On another OS, use an i386-win32 cross-compiler: `fpc -Pi386 -Twin32 -O2 FADeepProbe.dpr`.

The same source and Free Pascal version give a byte-identical `FADeepProbe.exe`.
