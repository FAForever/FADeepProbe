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
pcall(error, "FADeepProbe watchaddr 11502474 11502000+474", 0)
```
FA throws Lua errors as C++ exceptions, so FADeepProbe sees the request while the pcall swallows it.
Addresses are hex strings. An optional hex offset, such as `11502000+474`, keeps the structure's address in the log.
Each request replaces the previous one.

The `Watch:` section of the report logs each address by game tick: when it was armed, the first write by each instruction, and the write counts:
```
0x11502000+0x474 0 armed
0x11502000+0x474 120 first write by 0x0128E289, 0x00000004 -> 0x00000000, report 1
0x11502000+0x474 0-3779 writes:
    12 by ltable.c
    4214 by 0x0128E289, last value 0x00000000
```
Each first write gets a numbered report below the log, with the writer's registers, stack, Lua calls and code.
Lua's table code (`ltable.c`) is only counted, since Lua reuses memory often enough to use up the reports.
Values that change without a caught write, such as kernel writes, are logged when FADeepProbe polls them.

The `mods/FADeepProbeWatch` UI mod is an example, with a function to copy into your own hooks.

### Building
Requires [Free Pascal](https://www.freepascal.org/) 3.2.2 targeting i386-win32. All other compiler settings are in the source.
```
fpc -O2 FADeepProbe.dpr
```
On another OS, use an i386-win32 cross-compiler: `fpc -Pi386 -Twin32 -O2 FADeepProbe.dpr`.

The same source and Free Pascal version give a byte-identical `FADeepProbe.exe`.
