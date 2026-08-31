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
