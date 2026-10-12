# FADeepProbe
- In the case of a crash replaces BugSplat.
- Integrates with the FA log.
- Collects a lot more information.
- Can be placed between the client and the game.
- Protects the game from attaching a debugger.
- Does not affect performance.

### Usage
```
FADeepProbe.exe [exe_path] [/p <probe> ...] [/w <address> ...] [/<game_arg> ...]
```
- **`exe_path`**: Path to game executable.
  - Defaults to `ForgedAlliance.exe` in directory of FADeepProbe or `%ProgramData%\FAForever\bin\ForgedAlliance.exe`
- **`/p <probe> ...`**: Probe code addresses from the start. See [Probing code](#probing-code).
- **`/w <address> ...`**: Watch addresses from the start. See [Watching memory](#watching-memory).
- **`/<game_arg> ...`**: Arguments passed to the game.

Lua code can make the same requests while the game runs:
```lua
pcall(error, "FADeepProbe watchaddr 11502474 11502000+474", 0)
pcall(error, "FADeepProbe probe 438310:ecx+474", 0)
```
FA throws Lua errors as C++ exceptions, so FADeepProbe sees the request while the pcall swallows it.
All values are hex.

### Watching memory
FADeepProbe watches up to 4 dwords with hardware write breakpoints.
Each request replaces all watched addresses, even if it names fewer than 4. Watching 2 addresses and then 2 others leaves only the last 2.
A probe's watch expressions count as a request when the probe is hit. Addresses past the 4th aren't armed.
The log shows each replaced address as `disarmed by a new watch`.
An address can have an offset, such as `11502000+474`, which keeps the structure's address in the log.

### Probing code
A probe is a breakpoint on an instruction. FADeepProbe counts its hits and collects the C++ classes and Lua calls that reach it.
A probe can also watch addresses computed from the registers on its next hit, given after colons:
- `<register>[+<offset>]`, such as `ecx+474` for a field of the object a method is called on.
- `[<register>[+<offset>]][+<offset>]`, such as `[esp+4]+10` for a field of the object passed as the first stack argument.

Probing an address again replaces its watch expressions.

### Report
The `Watch:` section of the report logs each address by game tick:
```
0x00438310 0 probe armed, watches ecx+474 on the next hit
0x11502000+0x474 12 armed by probe 0x00438310 (ecx+474)
0x11502000+0x474 120 first write by 0x0128E289, 0x00000004 -> 0x00000000, report 1
0x11502000+0x474 12-3779 writes:
    0 by ltable.c
    4214 by 0x0128E289, last value 0x00000000
0x00438310 12-3779 3 hits
```
The first write to a watched address by each instruction gets a numbered report below the log, with the writer's registers, stack, Lua calls and code.
Lua's table code (`ltable.c`) is only counted, since Lua reuses memory often enough to use up the reports.
Values that change without a caught write, such as kernel writes, are logged when FADeepProbe polls them.
The callers of each probe follow the reports.

The `mods/FADeepProbeWatch` UI mod is an example, with functions to copy into your own hooks.

### Building
Requires [Free Pascal](https://www.freepascal.org/) 3.2.2 targeting i386-win32. All other compiler settings are in the source.
```
fpc -O2 FADeepProbe.dpr
```
On another OS, use an i386-win32 cross-compiler: `fpc -Pi386 -Twin32 -O2 FADeepProbe.dpr`.

The same source and Free Pascal version give a byte-identical `FADeepProbe.exe`.
