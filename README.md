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

### Building
Requires [Free Pascal](https://www.freepascal.org/) 3.2.2 targeting i386-win32. All other compiler settings are in the source.
```
fpc -O2 FADeepProbe.dpr
```
On another OS, use an i386-win32 cross-compiler: `fpc -Pi386 -Twin32 -O2 FADeepProbe.dpr`.

The same source and Free Pascal version give a byte-identical `FADeepProbe.exe`.
