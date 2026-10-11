"""Migrates FADeepProbe.dpr from Delphi to Free Pascal 3.2.2.

Usage: python fpc_transform.py FADeepProbe.dpr

Converts the file in place. Every replacement must match, so the script
stops instead of producing a source that silently behaves differently.
"""
import re
import sys

path = sys.argv[1]
with open(path, encoding='utf-8-sig') as f:
    s = f.read()


def sub(pattern, replacement):
    global s
    s, count = re.subn(pattern, replacement, s)
    if count == 0:
        sys.exit('pattern not found: ' + pattern)


# Delphi-only RTTI directives. Delphi mode with UTF-16 String, and the GUI subsystem
# so no console window opens, as Delphi does for programs without {$APPTYPE CONSOLE}.
sub(r'\{\$WEAKLINKRTTI ON\}\n\{\$RTTI [^}]*\}\n', '{$MODE DELPHIUNICODE}\n{$APPTYPE GUI}\n')

# FPC 3.2 has no dotted unit names and lacks a few declarations
sub(r'uses Winapi\.Windows;', '''uses Windows;

type
  PHMODULE=^HMODULE;
  NTSTATUS=LongInt;
  TOSVersionInfoExW=record
    dwOSVersionInfoSize,dwMajorVersion,dwMinorVersion,dwBuildNumber,dwPlatformId:DWORD;
    szCSDVersion:Array[0..127] of WideChar;
    wServicePackMajor,wServicePackMinor,wSuiteMask:Word;
    wProductType,wReserved:Byte;
  end;''')

# FPC's Windows unit maps the generic API names to the ANSI versions, but String and PChar are UTF-16 here
for name in ['GetEnvironmentVariable', 'FindFirstFile', 'CreateFile', 'CreateProcess',
             'MessageBox', 'SetConsoleTitle', 'GetModuleHandle', 'GetCommandLine']:
    sub(r'\b' + name + r'\b(?!W)', name + 'W')
sub(r'\bTWin32FindData\b', 'TWin32FindDataW')
sub(r'\bTStartupInfo\b', 'TStartupInfoW')

# FPC 3.2 has no inline var declarations: move the ones in WriteReport into its var block
sub(r'(procedure WriteReport;\nVar I:Int32;)',
    r'\1\n    hNtDll:HMODULE;\n    WineGetVersion:TWineGetVersion;\n    VI:TOSVersionInfoExW;')
sub(r'var hNtDll:=', 'hNtDll:=')
sub(r'  var WineGetVersion:TWineGetVersion;\n', '')
sub(r'  var VI:TOSVersionInfoExW;\n', '')
leftover = re.findall(r'^\s*var \w+\s*[:=]', s, re.M)
if leftover:
    sys.exit('unhandled inline var declarations: %r' % leftover)

# The source reads for-loop variables after the loop ends.
# Delphi leaves them at the last value + 1, FPC at the last value.
sub(r'for I:=Low\(Data\) to High\(Data\) do\n(\s*)if Data\[I\]=#0 then Break;\n',  # ReadStr
    r'I:=Low(Data);\n\1while (I<=High(Data)) and (Data[I]<>#0) do Inc(I);\n')
sub(r'for I:=I to High\(Data\) do',  # GetMiniDumpStr
    'for I:=SizeOf(Data) div 2 to High(Data) do')
sub(r'for I:=I to High\(Reports\) do\n(\s*)if Reports\[I\]\.ClassName=ClassName then\n',  # AddEventReport
    r'while I<=High(Reports) do\n\1if Reports[I].ClassName<>ClassName then Inc(I) else\n')

with open(path, 'w', encoding='utf-8', newline='\r\n') as f:
    f.write(s)
