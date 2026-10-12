program FADeepProbe;

{$MODE DELPHIUNICODE}
{$APPTYPE GUI}

{$SetPEFlags $0001}
{$SetPEFlags $0002}
{$SetPEFlags $0004}
{$SetPEFlags $0008}
{$SetPEFlags $0010}
{$SetPEFlags $0200}

uses Windows;

type
  PHMODULE=^HMODULE;
  NTSTATUS=LongInt;
  TOSVersionInfoExW=record
    dwOSVersionInfoSize,dwMajorVersion,dwMinorVersion,dwBuildNumber,dwPlatformId:DWORD;
    szCSDVersion:Array[0..127] of WideChar;
    wServicePackMajor,wServicePackMinor,wSuiteMask:Word;
    wProductType,wReserved:Byte;
  end;

type
  _MODULEINFO=record
    lpBaseOfDll:Pointer;
    SizeOfImage:DWORD;
    EntryPoint:Pointer;
  end;
  LPMODULEINFO=^_MODULEINFO;

  TBPState=Set of (BPSActive,BPSSingle);

  PBreakpoint=^TBreakpoint;
  TBreakpoint=record
    Ptr:Pointer;
    PrevByte,Tag:Byte;
    State:TBPState;
    function Enable:Boolean;
    function Disable:Boolean;
  end;
  TBreakpoints=TArray<TBreakpoint>;

  TEventReport=record
    ClassName:String;
    EntryPts:Array of record
      Pt,Prms:String;
    end;
  end;

  TWineGetVersion=function:PAnsiChar;stdcall;

var
  CmdLine,WorkDir,Str:String;
  SI:TStartupInfoW;
  PI:TProcessInformation;
  DbgEvent:TDebugEvent;
  SoftBPs:TBreakpoints;
  hThread:DWord;
  Context:TContext;
  ExceptionBP:TBreakpoint;
  LogFile:THandle;
  I:Int32;
  DbgActive:Boolean=True;
  ProfilePtr:UInt32=0;
  EventsCnt:UInt32=0;
  GameTick:UInt32=0;
  DLLs,DbgStrs:TArray<String>;
  MonitorReports,AVReports,CPPReports:TArray<TEventReport>;
  GameVer,BytesT:NativeUInt;

const
  THREAD_GET_CONTEXT=$0008;
  THREAD_SET_CONTEXT=$0010;

function OpenThread(dwDesiredAccess:DWord;bInheritHandle:Boolean;dwThreadId:DWORD):DWORD;stdcall;external 'kernel32.dll';
function K32EnumProcessModules(hProcess:THandle;lphModule:PHMODULE;cb:DWORD;var lpcbNeeded:DWORD):BOOL;stdcall;external 'kernel32.dll';
function K32GetModuleInformation(hProcess:THandle;hModule:HMODULE;lpmodinfo:LPMODULEINFO;cb:DWORD):BOOL;stdcall;external 'kernel32.dll';
function K32GetModuleBaseNameW(hProcess:THandle;hModule:HMODULE;lpBaseName:LPCWSTR;nSize:DWORD):DWORD;stdcall;external 'kernel32.dll';
function RtlGetVersion(var Info:TOSVersionInfoExW):NTSTATUS;stdcall;external 'ntdll.dll';

function GetEnvVar(const Name:String):String;
Var Size:UInt32;
begin
  Size:=GetEnvironmentVariableW(PChar(Name),nil,0);
  SetLength(Result,Size-1);
  GetEnvironmentVariableW(PChar(Name),PChar(Result),Size);
end;

function FileExists(const FileName:String):Boolean;
Var Data:TWin32FindDataW;
    hFile:THandle;
begin
  Result:=False;
  hFile:=FindFirstFileW(PChar(FileName),Data);
  if hFile<>INVALID_HANDLE_VALUE then
  begin
    FindClose(hFile);
    Result:=True;
  end;
end;

function GetFilePath(const FileName:String):String;
Var I:Integer;
begin
  for I:=Length(FileName) downto 1 do
    if FileName[I]='\' then
      Exit(Copy(FileName,1,I));
  Result:='';
end;

function GetFileNameExt(const FileName:String):String;
Var I:Integer;
begin
  for I:=Length(FileName) downto 1 do
    if FileName[I]='\' then Break;
  Result:=Copy(FileName,I+1,Length(FileName)-I);
end;

function IntToStr(Value:Integer):String;
Var V:Integer;
begin
  Result:='';
  V:=Abs(Value);
  repeat
    Result:=Chr(V mod 10+Ord('0'))+Result;
    V:=V div 10;
  until V=0;
  if Value<0 then Result:='-'+Result;
end;

function UIntToHex(Value:NativeUInt;Trunc:Boolean=False):String;
const HexChar:Array[0..15] of Char='0123456789ABCDEF';
Var B:PByte;
    I,I2:Integer;
begin
  I:=SizeOf(Value)*2;
  SetLength(Result,I);
  B:=@Value;
  for I2:=1 to SizeOf(Value) do
  begin
    Result[I]:=HexChar[B^ and 15]; Dec(I);
    Result[I]:=HexChar[B^ shr 4]; Dec(I);
    Inc(B);
  end;
  if Trunc then
  begin
    for I:=Low(Result) to High(Result) do
      if Result[I]<>'0' then
        Exit(Copy(Result,I,Length(Result)));
    Result:='0';
  end;
end;

function HexToUInt(const Str:String):NativeUInt;
Var I:Integer;
    C:NativeUInt;
begin
  Result:=0;
  for I:=Low(Str) to High(Str) do
  begin
    C:=Ord(Str[I]);
    if C in [48..57] then
      C:=C-48 else
    if C in [65..70] then
      C:=C-55 else
    if C in [97..102] then
      C:=C-87 else Continue;
    Result:=Result shl 4+C;
  end;
end;

function FloatToStr(Value:Single;Digits:Byte):String;
const
  Pow10Tab:Array[0..8] of Integer=(1,10,100,1000,10000,100000,1000000,10000000,100000000);

Var B:Boolean;
    V:Single;
    I,I2,I3,L1,L2:Integer;
    S1,S2:Array[0..9] of Char;
    P1,P2:PChar;
begin
  if Value<>Value then Exit('Nan') else
  if Value>MaxInt then Exit('+Oversize') else
  if Value<-MaxInt then Exit('-Oversize') else
  if Value=1/0 then Exit('+Inf') else
  if Value=-1/0 then Exit('-Inf');
  B:=Value<0;
  Value:=Abs(Value);
  I:=Trunc(Value);
  I2:=Pow10Tab[Digits];
  V:=(Value-I)*I2;
  I3:=Round(V);
  if I3>=I2 then
  begin
    Inc(I);
    I3:=0;
  end;
  P1:=@S1[High(S1)]; P1^:=#0;Dec(P1);
  repeat
    P1^:=Chr(I mod 10+Ord('0'));
    I:=I div 10;
    Dec(P1);
  until I=0;
  if B then P1^:='-' else Inc(P1);
  if I3<=0 then Exit(P1);
  P2:=@S2[High(S2)];
  I2:=0;
  repeat
    P2^:=Chr(I3 mod 10+Ord('0'));
    I3:=I3 div 10;
    Dec(P2);
    Inc(I2);
  until I3=0;
  for I2:=1 to Digits-I2 do
  begin
    P2^:='0';
    Dec(P2);
  end;
  for I2:=High(S2) downto Low(S2) do
    if S2[I2]<>'0' then Break;
  P2^:='.';
  L1:=@S1[High(S1)]-P1;
  L2:=@S2[I2]-P2+1;
  SetLength(Result,L1+L2);
  Move(P1^,Result[1],L1*SizeOf(Char));
  Move(P2^,Result[1+L1],L2*SizeOf(Char));
end;

function ReadDllName(const Data:TLoadDLLDebugInfo):String;
Var BytesT:NativeUInt;
    Ptr:Pointer;
    StrW:String;
    StrA:AnsiString;
begin
  if not ReadProcessMemory(PI.hProcess,Data.lpImageName,@Ptr,4,BytesT) then Exit('');
  if Data.fUnicode<>0 then
  begin
    SetLength(StrW,255);
    ReadProcessMemory(PI.hProcess,Ptr,@StrW[1],255*SizeOf(Char),BytesT);
    Exit(PChar(@StrW[1]));
  end;
  SetLength(StrA,255);
  ReadProcessMemory(PI.hProcess,Ptr,@StrA[1],255,BytesT);
  Result:=PAnsiChar(@StrA[1]);
end;

function ReadDebugString(const Data:TOutputDebugStringInfo):String;
Var BytesT:NativeUInt;
    Ptr:Pointer;
    StrW:String;
    StrA:AnsiString;
begin
  Ptr:=Data.lpDebugStringData;
  if Data.fUnicode<>0 then
  begin
    SetLength(StrW,Data.nDebugStringLength);
    ReadProcessMemory(PI.hProcess,Ptr,@StrW[1],Length(StrW)*SizeOf(Char),BytesT);
    Exit(PChar(@StrW[1]));
  end;
  SetLength(StrA,Data.nDebugStringLength);
  ReadProcessMemory(PI.hProcess,Ptr,@StrA[1],Length(StrA),BytesT);
  Result:=PAnsiChar(@StrA[1]);
end;

function TBreakpoint.Enable:Boolean;
Var Data:Byte;
    BytesT:NativeUInt;
begin
  Result:=False;
  Data:=$CC;
  WriteProcessMemory(PI.hProcess,Ptr,@Data,1,BytesT);
  if BytesT<>1 then
  begin
    MessageBoxW(0,'TBreakpoint.Enable->WriteProcessMemory','Error',MB_ICONERROR);
    Halt;
  end;
  FlushInstructionCache(PI.hProcess,Ptr,1);
  Include(State,BPSActive);
  Result:=True;
end;

function TBreakpoint.Disable:Boolean;
Var BytesT:NativeUInt;
begin
  Result:=False;
  WriteProcessMemory(PI.hProcess,Ptr,@PrevByte,1,BytesT);
  if BytesT<>1 then
  begin
    MessageBoxW(0,'TBreakpoint.Disable->WriteProcessMemory','Error',MB_ICONERROR);
    Halt;
  end;
  FlushInstructionCache(PI.hProcess,Ptr,1);
  Exclude(State,BPSActive);
  Result:=True;
end;

function AddSoftBP(Ptr:Pointer;Tag:Byte;State:TBPState):Boolean;
Var I:Int32;
    Data:Byte;
    BytesT:NativeUInt;
begin
  Result:=False;
  for I:=Low(SoftBPs) to High(SoftBPs) do
    if SoftBPs[I].Ptr=Ptr then Exit(True);
  ReadProcessMemory(PI.hProcess,Ptr,@Data,1,BytesT);
  if BytesT<>1 then
  begin
    MessageBoxW(0,'AddSoftBP->ReadProcessMemory','Error',MB_ICONERROR);
    Halt;
  end;
  SetLength(SoftBPs,Length(SoftBPs)+1);
  SoftBPs[High(SoftBPs)].Ptr:=Ptr;
  SoftBPs[High(SoftBPs)].PrevByte:=Data;
  SoftBPs[High(SoftBPs)].Tag:=Tag;
  SoftBPs[High(SoftBPs)].State:=State;
  if BPSActive in State then
    Result:=SoftBPs[High(SoftBPs)].Enable else
    Result:=True;
end;

function DelSoftBP(Ptr:Pointer;out OutBP:TBreakpoint):Boolean;
Var I:Integer;
begin
  for I:=Low(SoftBPs) to High(SoftBPs) do
    if SoftBPs[I].Ptr=Ptr then
    begin
      if BPSActive in SoftBPs[I].State then
        SoftBPs[I].Disable;
      OutBP:=SoftBPs[I];
      SoftBPs[I]:=SoftBPs[High(SoftBPs)];
      SetLength(SoftBPs,High(SoftBPs));
      Exit(True);
    end;
  Result:=False;
end;

function StackWalk(Ptr:PDWord;Steps:UInt32):TArray<PByte>;
Var Data:Array[1..20] of DWord;
    BytesT:NativeUInt;
    I:UInt32;
    P:PDWord;
    W:Word;
label Next;
begin
  Result:=nil;
  while True do
  begin
    if not ReadProcessMemory(PI.hProcess,Ptr,@Data,SizeOf(Data),BytesT) then Exit;
    P:=@Data;
    for I:=Low(Data) to High(Data) do
    begin
      if ReadProcessMemory(PI.hProcess,PByte(P^)-5,@W,SizeOf(W),BytesT) then
        if Byte(W)=$E8 then
        begin
          Result:=Result+[PByte(P^)-5];
          if Steps>1 then
            Dec(Steps) else Exit;
          Goto Next;
        end;
      if ReadProcessMemory(PI.hProcess,PByte(P^)-2,@W,SizeOf(W),BytesT) then
        if (Byte(W)=$FF) and (W>=$D0FF) and (W<=$D7FF) then
        begin
          Result:=Result+[PByte(P^)-2];
          if Steps>1 then
            Dec(Steps) else Exit;
          Goto Next;
        end;
      if ReadProcessMemory(PI.hProcess,PByte(P^)-6,@W,SizeOf(W),BytesT) then
        if W=$15FF then
        begin
          Result:=Result+[PByte(P^)-6];
          if Steps>1 then
            Dec(Steps) else Exit;
          Goto Next;
        end;
Next: Inc(P);
    end;
    Inc(Ptr,Length(Data));
  end;
end;

function GetTypeNamePtr(SelfPtr:NativeUInt):NativeUInt;
Var BytesT:NativeUInt;
begin {$Q-}
  Result:=0;
  if not ReadProcessMemory(PI.hProcess,Pointer(SelfPtr),@SelfPtr,SizeOf(SelfPtr),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(SelfPtr-$4),@SelfPtr,SizeOf(SelfPtr),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(SelfPtr+$C),@SelfPtr,SizeOf(SelfPtr),BytesT) then Exit;
  Result:=SelfPtr+8;
  if not ReadProcessMemory(PI.hProcess,Pointer(Result),@SelfPtr,SizeOf(SelfPtr),BytesT) then Exit(0);
  if Byte(SelfPtr)<>$2E then Exit(0);
end;

function ReadStr(Ptr:NativeUInt;Len:UInt32=256):UTF8String;
Var BytesT:NativeUInt;
    Data:Array[1..50] of UTF8Char;
    I:Integer;
begin
  Result:='';
  while True do
  begin
    if not ReadProcessMemory(PI.hProcess,Pointer(Ptr),@Data,SizeOf(Data),BytesT) then Exit;
    I:=Low(Data);
      while (I<=High(Data)) and (Data[I]<>#0) do Inc(I);
    Dec(I);
    Result:=Result+Copy(Data,Low(Data),I);
    if I<Length(Data) then Exit;
    Ptr:=Ptr+SizeOf(Data);
    Len:=Len-SizeOf(Data);
    if Len<1 then Exit;
  end;
end;

function GetClassName(SelfPtr:NativeUInt):UTF8String;
Var I:Int32;
begin
  SelfPtr:=GetTypeNamePtr(SelfPtr);
  if SelfPtr=0 then Exit('');
  Result:=ReadStr(SelfPtr);
  for I:=Low(Result) to High(Result) do
    if Result[I]<#33 then Exit('');
end;

function ReadLuaStr(Ptr:NativeUInt):UTF8String;
Var BytesT,V:NativeUInt;
begin
  Result:='';
  if not ReadProcessMemory(PI.hProcess,Pointer(Ptr+$10),@V,SizeOf(V),BytesT) then Exit;
  Result:=ReadStr(Ptr+$14,V);
end;

function ReadFAStr(Ptr:NativeUInt):UTF8String;
Var BytesT,V:NativeUInt;
begin
  Result:='';
  if not ReadProcessMemory(PI.hProcess,Pointer(Ptr+$14),@V,SizeOf(V),BytesT) then Exit;
  if V<=16 then Ptr:=Ptr+$4 else
    if not ReadProcessMemory(PI.hProcess,Pointer(Ptr+$4),@Ptr,SizeOf(Ptr),BytesT) then Exit;
  Result:=ReadStr(Ptr,V);
end;

function lStateType(lua_State:NativeUInt):Int32;
Var BytesT,LPState,V:NativeUInt;
begin
  Result:=0;
  if not ReadProcessMemory(PI.hProcess,Pointer(lua_State+$44),@LPState,SizeOf(LPState),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(LPState),@V,SizeOf(V),BytesT) then Exit;
  if lua_State<>V then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(LPState+$20),@V,SizeOf(V),BytesT) then Exit;
  if LPState=V then Exit(1);
  Result:=2;
end;

const
  LuaVExecuteSEH=$B5CA48; //SEH handler installed by luaV_execute

//luaV_execute keeps the pc of the running Lua function in a local and only
//stores it to CallInfo.savedpc around calls, so savedpc of the innermost frame is stale.
//Finds the luaV_execute frame of lua_State through its SEH record on the stack
//and returns the address of the instruction being executed, or 0.
function GetLuaExecutePC(lua_State,Esp:NativeUInt):NativeUInt;
Var Data:Array[0..255] of NativeUInt;
    BytesT,Ptr,Rec,V:NativeUInt;
    I,Chunks:Int32;
begin
  Result:=0;
  Ptr:=Esp;
  for Chunks:=1 to 64 do
  begin
    if not ReadProcessMemory(PI.hProcess,Pointer(Ptr),@Data,SizeOf(Data),BytesT) then Exit;
    for I:=Low(Data) to High(Data) do
      if Data[I]=LuaVExecuteSEH then
      begin
        //push -1; push SEH; push fs:[0] after "and esp,-8", so the record is 0xC below the aligned ebp
        Rec:=Ptr+NativeUInt(I)*SizeOf(NativeUInt)-4;
        //L is the first argument, at ebp+8, and ebp is the aligned ebp or 4 above it
        if not ReadProcessMemory(PI.hProcess,Pointer(Rec+$14),@V,SizeOf(V),BytesT) then Continue;
        if V<>lua_State then
          if not ReadProcessMemory(PI.hProcess,Pointer(Rec+$18),@V,SizeOf(V),BytesT)
          or (V<>lua_State) then Continue;
        //Locals start 0x5C below the record, the pc of the next instruction is at locals+0x10
        if not ReadProcessMemory(PI.hProcess,Pointer(Rec-$4C),@V,SizeOf(V),BytesT) then Exit;
        Exit(V-4);
      end;
    Ptr:=Ptr+SizeOf(Data);
  end;
end;

//When LivePC is set, PC must be a pc from GetLuaExecutePC: Lua functions without one return ''.
function GetLuaCallStr(CI:NativeUInt;PC:NativeUInt=0;LivePC:Boolean=False):String;
Var BytesT,Closure,Proto,Ptr,V:NativeUInt;
begin
  Result:='';
  if not ReadProcessMemory(PI.hProcess,Pointer(CI),@Ptr,SizeOf(Ptr),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(Ptr-$4),@Closure,SizeOf(Closure),BytesT) then Exit;

  if not ReadProcessMemory(PI.hProcess,Pointer(Ptr-$8),@V,SizeOf(V),BytesT) then Exit;
  if V=6 then
  begin
    if not ReadProcessMemory(PI.hProcess,Pointer(Closure+$10),@V,SizeOf(V),BytesT) then Exit;
    Exit('@CFunc: 0x'+UIntToHex(V));
  end;
  if LivePC and (PC=0) then Exit;

  if not ReadProcessMemory(PI.hProcess,Pointer(Closure+$18),@Proto,SizeOf(Proto),BytesT) then Exit;

  if not ReadProcessMemory(PI.hProcess,Pointer(Proto+$20),@Ptr,SizeOf(Ptr),BytesT) then Exit;
  Result:=ReadLuaStr(Ptr);
  if (Result='') or (Result[1]<>'@') then Exit;

  if not LivePC then
    if not ReadProcessMemory(PI.hProcess,Pointer(CI+$C),@PC,SizeOf(PC),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(Proto+$C),@CI,SizeOf(CI),BytesT) then Exit;
  Ptr:=PC-CI;
  if not ReadProcessMemory(PI.hProcess,Pointer(Proto+$30),@V,SizeOf(V),BytesT) then Exit;
  if Ptr div 4>=V then //pc is not inside this function
  begin
    if LivePC then Result:='';
    Exit;
  end;
  if not ReadProcessMemory(PI.hProcess,Pointer(Proto+$14),@CI,SizeOf(CI),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(Ptr+CI),@V,SizeOf(V),BytesT) then Exit;
  Result:=Result+' '+IntToStr(V);
end;

function GetLuaFuncPtStr(Closure:NativeUInt):String;
Var BytesT,Ptr,V:NativeUInt;
begin
  Result:='';
  if not ReadProcessMemory(PI.hProcess,Pointer(Closure+$18),@Closure,SizeOf(Closure),BytesT) then Exit;

  if not ReadProcessMemory(PI.hProcess,Pointer(Closure+$20),@Ptr,SizeOf(Ptr),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(Ptr+$14),@V,SizeOf(V),BytesT) then Exit;
  if Byte(V)<>$40 then Exit;
  Result:=ReadLuaStr(Ptr);

  if not ReadProcessMemory(PI.hProcess,Pointer(Closure+$3C),@V,SizeOf(V),BytesT) then Exit;
  Result:=Result+' '+IntToStr(V);
end;

function Demangle(const Str:String):String;
begin
  Result:=Str;
end;

function Get_c_object(TablePtr:NativeUInt):NativeUInt;
Var BytesT,S,E,V:NativeUInt;
    Str:String;
begin
  Result:=0;
  if not ReadProcessMemory(PI.hProcess,Pointer(TablePtr+$14),@S,SizeOf(S),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(TablePtr+$18),@E,SizeOf(E),BytesT) then Exit;
  while S<E do
  begin
    if not ReadProcessMemory(PI.hProcess,Pointer(S),@V,SizeOf(V),BytesT) then Exit;
    if V=4 then
    begin
      if not ReadProcessMemory(PI.hProcess,Pointer(S+$4),@V,SizeOf(V),BytesT) then Exit;
      Str:=ReadLuaStr(V);
      if Str='_c_object' then
      begin
        if not ReadProcessMemory(PI.hProcess,Pointer(S+$C),@V,SizeOf(V),BytesT) then Exit;
        if not ReadProcessMemory(PI.hProcess,Pointer(V+$10),@V,SizeOf(V),BytesT) then Exit;
        Exit(V);
      end;
    end;
    S:=S+$14;
  end;
end;

function GetTrueCObjectPtr(SelfPtr:NativeUInt):NativeUInt;
Var BytesT,V:NativeUInt;
begin
  Result:=0;
  if not ReadProcessMemory(PI.hProcess,Pointer(SelfPtr),@V,SizeOf(V),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(V-$4),@V,SizeOf(V),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(V+$4),@V,SizeOf(V),BytesT) then Exit;
  Result:=SelfPtr-V;
end;

function FindAncestor(SelfPtr:NativeUInt;const A:TArray<NativeUInt>):Int32;
Var Data:Array[1..10] of NativeUInt;
    BytesT:NativeUInt;
    I,I2:Int32;
begin
  Result:=-1;
  if not ReadProcessMemory(PI.hProcess,Pointer(SelfPtr),@SelfPtr,SizeOf(SelfPtr),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(SelfPtr-$4),@SelfPtr,SizeOf(SelfPtr),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(SelfPtr+$24),@Data,SizeOf(Data),BytesT) then Exit;
  for I:=Low(Data) to High(Data) do
  begin
    if not ReadProcessMemory(PI.hProcess,Pointer(Data[I]),@SelfPtr,SizeOf(SelfPtr),BytesT) then Exit;
    for I2:=Low(A) to High(A) do
      if A[I2]=SelfPtr then Exit(I2);
  end;
end;

function GetCObjectInfo(SelfPtr:NativeUInt):String;
Var A:TArray<NativeUInt>;
    BytesT,V:NativeUInt;
    Str:String;
    I:Int32;

  function GetBpName(SelfPtr:NativeUInt):String;
  begin
    if SelfPtr=0 then
    begin
      Result:=' BpName:None';
      Exit;
    end;
    Result:=ReadFAStr(SelfPtr+$8);
    if Result='' then
      Result:=' BpName:Wrong' else
      Result:=' BpName:'+Result;
  end;
begin
  Result:=GetClassName(SelfPtr);
  if Result='' then Exit;
  Result:=Demangle(Result);
  SelfPtr:=GetTrueCObjectPtr(SelfPtr);
  A:=[$F6B810,$F8C018,$F65214,$F6A654];
  I:=FindAncestor(SelfPtr,A);
  case I of
    0: SelfPtr:=SelfPtr+$70;
    1: SelfPtr:=SelfPtr+$44;
    2: begin
      Result:=Result+GetBpName(SelfPtr);
      Exit;
    end;
    3: begin
      if not ReadProcessMemory(PI.hProcess,Pointer(SelfPtr+$1C),@V,SizeOf(V),BytesT) then Exit;
      Result:=Result+#13+'  Owner: '+GetCObjectInfo(V);
      V:=GetTypeNamePtr(SelfPtr);
      case V of
        $F6FD80: begin
          if not ReadProcessMemory(PI.hProcess,Pointer(SelfPtr+$48),@V,SizeOf(V),BytesT) then Exit;
          Result:=Result+#13+'  Target: '+GetCObjectInfo(V-4);
        end;
        $F6FDCC: begin
          if not ReadProcessMemory(PI.hProcess,Pointer(SelfPtr+$88),@V,SizeOf(V),BytesT) then Exit;
          Result:=Result+#13+'  Target: '+GetCObjectInfo(V-4);
        end;
      end;
      Exit;
    end;
  else
    Exit;
  end;
  if not ReadProcessMemory(PI.hProcess,Pointer(SelfPtr),@V,SizeOf(V),BytesT) then Exit;
  Result:=Result+' ID:'+IntToStr(V);
  if not ReadProcessMemory(PI.hProcess,Pointer(SelfPtr+4),@V,SizeOf(V),BytesT) then Exit;
  Result:=Result+GetBpName(V);
end;

function GetLuaCallPrmsStr(S,E:NativeUInt):String;
Var BytesT,T,V:NativeUInt;
begin
  Result:='';
  while S<E do
  begin
    if not ReadProcessMemory(PI.hProcess,Pointer(S),@T,SizeOf(T),BytesT) then Exit;
    if not ReadProcessMemory(PI.hProcess,Pointer(S+$4),@V,SizeOf(V),BytesT) then Exit;
    if Result<>'' then
      Result:=Result+', ';
    case T of
      0: Result:=Result+'nil';
      1: if V=0 then
        Result:=Result+'false' else
        Result:=Result+'true';
      2: Result:=Result+'LightUData:'+UIntToHex(V);
      3: Result:=Result+FloatToStr(PSingle(@V)^,6);
      4: Result:=Result+'"'+ReadLuaStr(V)+'"';
      5: begin
        T:=Get_c_object(V);
        if T>0 then
          Result:=Result+'CObject:'+GetCObjectInfo(T) else
          Result:=Result+'Table'; //:'+UIntToHex(V);
      end;
      6: Result:=Result+'CFunc'; //:'+UIntToHex(V);
      7: Result:=Result+'Func:'+GetLuaFuncPtStr(V);
      8: Result:=Result+'UData:'+UIntToHex(V);
      9: Result:=Result+'Thread'; //:'+UIntToHex(V);
    else
      Exit;
    end;
    S:=S+8;
  end;
end;

function GetCallsReport(lua_State,Esp:NativeUInt):String;
Var S,E,SE,FS,FE,PC:NativeUInt;
    Str,LineStr:String;
begin
  Result:='';
  if not ReadProcessMemory(PI.hProcess,Pointer(lua_State+$14),@E,SizeOf(E),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(lua_State+$28),@S,SizeOf(S),BytesT) then Exit;
  if E<S+$28 then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(lua_State+$8),@SE,SizeOf(SE),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(S),@FS,SizeOf(FS),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(FS+$4),@FS,SizeOf(FS),BytesT) then Exit;
  Result:=GetLuaFuncPtStr(FS);
  S:=S+$28;
  while S<=E do
  begin
    if not ReadProcessMemory(PI.hProcess,Pointer(S),@FS,SizeOf(FS),BytesT) then Exit;
    S:=S+$28;
    if S<=E then
    begin
      if not ReadProcessMemory(PI.hProcess,Pointer(S),@FE,SizeOf(FE),BytesT) then Exit;
      Str:=GetLuaCallPrmsStr(FS,FE-$8);
      if Str='' then
        Str:=GetLuaCallStr(S-$28) else
        Str:=Str+#13+GetLuaCallStr(S-$28);
    end else
    begin
      Str:=GetLuaCallPrmsStr(FS,SE);
      PC:=0;
      if ReadProcessMemory(PI.hProcess,Pointer(FS-$8),@FE,SizeOf(FE),BytesT) and (FE=7) then
        PC:=GetLuaExecutePC(lua_State,Esp);
      LineStr:=GetLuaCallStr(S-$28,PC,True);
      if Str='' then
        Str:=LineStr else
      if LineStr<>'' then
        Str:=Str+#13+LineStr;
    end;
    Result:=Result+#13+Str;
  end;
end;

function BPExceptionHandling(Ptr:Pointer;out OutBP:TBreakpoint):Boolean;
Var I:Integer;
begin
  for I:=High(SoftBPs) downto Low(SoftBPs) do
    if SoftBPs[I].Ptr=Ptr then
    begin
      OutBP:=SoftBPs[I];
      if BPSActive in SoftBPs[I].State then
        SoftBPs[I].Disable;
      if BPSSingle in SoftBPs[I].State then
      begin
        SoftBPs[I]:=SoftBPs[High(SoftBPs)];
        SetLength(SoftBPs,High(SoftBPs));
      end;
      Exit(True);
    end;
  Result:=False;
end;

function StacktraceToStr(const Calls:TArray<PByte>):String;
Var Modules:Array[0..200] of HMODULE;
    cbNeeded:DWORD;
    I,I2:Int32;
    Ptr:NativeUInt;
    MInfo:_MODULEINFO;
    MName:Array[0..255] of Char;
begin
  Result:='';
  K32EnumProcessModules(PI.hProcess,@Modules,SizeOf(Modules),cbNeeded);
  for I:=Low(Calls) to High(Calls) do
  begin
    Result:=Result+' ';
    Ptr:=NativeUInt(Calls[I]);
    for I2:=1 to (cbNeeded div SizeOf(HMODULE)-1) do
    begin
      K32GetModuleInformation(PI.hProcess,Modules[I2],@MInfo,SizeOf(MInfo));
      if (Ptr>=NativeUInt(MInfo.lpBaseOfDll))
      and (Ptr<NativeUInt(MInfo.lpBaseOfDll)+MInfo.SizeOfImage) then
      begin
        K32GetModuleBaseNameW(PI.hProcess,Modules[I2],@MName,Length(MName));
        Result:=Result+MName+'+';
        Ptr:=Ptr-NativeUInt(MInfo.lpBaseOfDll);
        Break;
      end;
    end;
    Result:=Result+'0x'+UIntToHex(Ptr);
  end;
end;

function GetMiniDumpStr(Ptr:Pointer):String;
  procedure ByteToHex(B:Byte);
  const HexChar:Array[0..15] of Char='0123456789ABCDEF';
  begin
    Result:=Result+HexChar[B shr 4]+HexChar[B and 15];
  end;

Var Data:Array[0..$7F] of Byte;
    BytesT:NativeUInt;
    I:Int32;
begin
  Dec(NativeUInt(Ptr),SizeOf(Data) div 2);
  Result:='From 0x'+UIntToHex(NativeUInt(Ptr))+' to 0x'+UIntToHex(NativeUInt(Ptr)+SizeOf(Data))+#13;
  if not ReadProcessMemory(PI.hProcess,Ptr,@Data,SizeOf(Data),BytesT) then Exit;
  for I:=Low(Data) to (SizeOf(Data) div 2-1) do
    ByteToHex(Data[I]);
  Result:=Result+#13;
  for I:=SizeOf(Data) div 2 to High(Data) do
    ByteToHex(Data[I]);
end;

function FindStr(const Strs:Array of String;const Str:String):Int32;
Var I:Int32;
begin
  for I:=Low(Strs) to High(Strs) do
    if Strs[I]=Str then Exit(I);
  Result:=-1;
end;

procedure AddEventReport(var Reports:TArray<TEventReport>;const ClassName,Pt,Prms:String);
Var I,I2:Int32;
begin
  I:=Low(Reports);
  while I<=High(Reports) do
    if Reports[I].ClassName<>ClassName then Inc(I) else
    with Reports[I] do
    begin
      for I2:=Low(EntryPts) to High(EntryPts) do
        if EntryPts[I2].Pt=Pt then
        begin
          if EntryPts[I2].Prms='' then
            EntryPts[I2].Prms:=Prms;
          Exit;
        end;
      Break;
    end;
  if I=Length(Reports) then
  begin
    SetLength(Reports,I+1);
    Reports[I].ClassName:=ClassName;
  end;
  if (Pt='') and (Prms='') then Exit;
  with Reports[I] do
  begin
    SetLength(EntryPts,Length(EntryPts)+1);
    EntryPts[High(EntryPts)].Pt:=Pt;
    EntryPts[High(EntryPts)].Prms:=Prms;
  end;
end;

const
  LTableCodeStart=$926F70; //luaH_mainposition, first function of ltable.c
  LTableCodeEnd=$927B09;   //End of luaH_setnum, last function of ltable.c
  LuaNodeSize=$14;
  MaxDumpNodes=1024;

type
  TLuaTable=packed record
    Next:DWord;
    TT,Marked,Pad1,Pad2:Byte;
    Flags,LSizeNode,Pad3,Pad4:Byte;
    Metatable,ArrayPtr,Node,FirstFree,GCList,SizeArray:DWord;
  end;
  TLuaNode=packed record
    KeyTT,KeyV,ValTT,ValV,Next:DWord;
  end;

//Index of a node pointer in the node array of T, or -1
function LuaNodeIndex(const T:TLuaTable;P:DWord):Int32;
begin
  if (P>=T.Node) and ((P-T.Node) mod LuaNodeSize=0)
  and ((P-T.Node) div LuaNodeSize<(DWord(1) shl T.LSizeNode)) then
    Result:=(P-T.Node) div LuaNodeSize else
    Result:=-1;
end;

//True if Ptr is readable and has the table type tag
function ReadLuaTable(Ptr:NativeUInt;out T:TLuaTable):Boolean;
Var BytesT:NativeUInt;
begin
  Result:=ReadProcessMemory(PI.hProcess,Pointer(Ptr),@T,SizeOf(T),BytesT) and (T.TT=5);
end;

//True if the node array fields of T are consistent
function IsLuaTableHeaderValid(const T:TLuaTable):Boolean;
begin
  Result:=(T.LSizeNode<=24) and (T.Node<>0) and (LuaNodeIndex(T,T.FirstFree)>=0);
end;

function LuaValueStr(TT,V:DWord):String;
Var BytesT,Len:NativeUInt;
begin
  case TT of
    0: Result:='nil';
    1: if V=0 then
      Result:='false' else
      Result:='true';
    2: Result:='LightUData:'+UIntToHex(V);
    3: Result:=FloatToStr(PSingle(@V)^,6);
    4: if ReadProcessMemory(PI.hProcess,Pointer(V+$10),@Len,SizeOf(Len),BytesT) and (Len<=64) then
      Result:='"'+ReadLuaStr(V)+'"' else
      Result:='String:'+UIntToHex(V);
    5: Result:='Table:'+UIntToHex(V);
    6: Result:='CFunc:'+UIntToHex(V);
    7: Result:='Func:'+UIntToHex(V);
    8: Result:='UData:'+UIntToHex(V);
    9: Result:='Thread:'+UIntToHex(V);
  else
    Result:='Type'+IntToStr(TT)+':'+UIntToHex(V);
  end;
end;

//Node index luaH_mainposition gives the key, or -1 if unknown
function LuaMainPosition(TT,V:DWord;LSizeNode:Byte):Int32;
Var BytesT:NativeUInt;
    Mask,Hash:DWord;
    F:Single;
begin
  Mask:=(DWord(1) shl LSizeNode)-1;
  case TT of
    0: Exit(-1);
    1: Exit(V and Mask);
    3: begin
      F:=PSingle(@V)^+1; //Numbers are hashed as key+1.0
      Hash:=PDWord(@F)^;
    end;
    4: begin
      if not ReadProcessMemory(PI.hProcess,Pointer(V+$C),@Hash,SizeOf(Hash),BytesT) then Exit(-1);
      Exit(Hash and Mask);
    end;
  else
    Hash:=V;
  end;
  Result:=Hash mod (Mask or 1);
end;

//Lists the hash part of a table: each node with its main position and its raw dwords.
//Keys that luaH_get can't reach by walking the chain from their main position are marked UNREACHABLE.
//Nodes with a nil key and a non-nil value, which Lua never creates, are marked NIL KEY.
function GetLuaTableDumpStr(Ptr:NativeUInt;const T:TLuaTable):String;
Var Nodes:Array of TLuaNode;
    Readable:Array of Boolean;
    BytesT,Size,Cnt:NativeUInt;
    I,Main,Cur,Steps,Unreachable,NilKeys:Int32;
    P:DWord;
    Line:String;

  function NodePtrStr(P:DWord):String;
  begin
    if P=0 then Exit('nil');
    if LuaNodeIndex(T,P)>=0 then
      Result:='['+IntToStr(LuaNodeIndex(T,P))+']' else
      Result:='0x'+UIntToHex(P);
  end;
begin
  Result:='Table 0x'+UIntToHex(Ptr)+', flags 0x'+UIntToHex(T.Flags,True)
    +', metatable 0x'+UIntToHex(T.Metatable)
    +', array 0x'+UIntToHex(T.ArrayPtr)+' size '+IntToStr(T.SizeArray)+#13
    +'Header {';
  for I:=0 to SizeOf(T) div 4-1 do
  begin
    if I>0 then Result:=Result+' ';
    Result:=Result+UIntToHex(PDWord(PByte(@T)+I*4)^);
  end;
  Result:=Result+'}';
  if (T.LSizeNode>24) or (T.Node=0) then
    Exit(Result+#13+'Invalid lsizenode or node');
  Size:=NativeUInt(1) shl T.LSizeNode;
  Result:=Result+#13+'Node 0x'+UIntToHex(T.Node)+' size '+IntToStr(Size)+', firstfree '+NodePtrStr(T.FirstFree);
  if LuaNodeIndex(T,T.FirstFree)<0 then
    Result:=Result+' (outside the node array)';
  Cnt:=Size;
  if Cnt>MaxDumpNodes then
  begin
    Cnt:=MaxDumpNodes;
    Result:=Result+#13+'Only the first '+IntToStr(Cnt)+' nodes, chains not checked';
  end;
  SetLength(Nodes,Cnt);
  SetLength(Readable,Cnt);
  if ReadProcessMemory(PI.hProcess,Pointer(T.Node),@Nodes[0],Cnt*SizeOf(TLuaNode),BytesT) then
    for I:=0 to Cnt-1 do
      Readable[I]:=True
  else //The node array may be partly unmapped, read nodes one by one
    for I:=0 to Cnt-1 do
      Readable[I]:=ReadProcessMemory(PI.hProcess,Pointer(T.Node+NativeUInt(I)*LuaNodeSize),
        @Nodes[I],SizeOf(TLuaNode),BytesT);
  Unreachable:=0;
  NilKeys:=0;
  for I:=0 to Cnt-1 do
  with Nodes[I] do
  begin
    if not Readable[I] then
    begin
      Result:=Result+#13+'['+IntToStr(I)+'] unreadable';
      Continue;
    end;
    if (KeyTT=0) and (KeyV=0) and (ValTT=0) and (ValV=0) and (Next=0) then Continue;
    Line:='['+IntToStr(I)+'] '+LuaValueStr(KeyTT,KeyV)+' = '+LuaValueStr(ValTT,ValV)
      +', next '+NodePtrStr(Next);
    if KeyTT<>0 then
    begin
      Main:=LuaMainPosition(KeyTT,KeyV,T.LSizeNode);
      if Main<0 then
        Line:=Line+', main ?' else
      begin
        Line:=Line+', main ['+IntToStr(Main)+']';
        if Cnt=Size then
        begin
          Cur:=Main;
          Steps:=0;
          while (Cur>=0) and (Cur<>I) and (Steps<Cnt) do
          begin
            P:=Nodes[Cur].Next;
            if (P=0) or not Readable[Cur] then
              Cur:=-1 else
              Cur:=LuaNodeIndex(T,P);
            Inc(Steps);
          end;
          if Cur<>I then
          begin
            Line:=Line+' UNREACHABLE';
            Inc(Unreachable);
          end;
        end;
      end;
    end
    else if ValTT<>0 then
    begin
      Line:=Line+' NIL KEY';
      Inc(NilKeys);
    end;
    Result:=Result+#13+Line+'  {'+UIntToHex(KeyTT)+' '+UIntToHex(KeyV)+' '
      +UIntToHex(ValTT)+' '+UIntToHex(ValV)+' '+UIntToHex(Next)+'}';
  end;
  if Cnt=Size then
    Result:=Result+#13+'Unreachable keys: '+IntToStr(Unreachable);
  Result:=Result+#13+'Nil keys with values: '+IntToStr(NilKeys);
end;

//Dumps the Lua tables referenced by the registers and the top 16 stack slots
procedure DumpLuaTables(var Reports:TArray<TEventReport>;const Context:TContext);
const RegNames:Array[0..6] of String=('EBX','ESI','EDI','EAX','ECX','EDX','EBP');
Var Ptrs:Array[0..22] of NativeUInt;
    Done:TArray<NativeUInt>;
    BytesT:NativeUInt;
    T:TLuaTable;
    I:Int32;
    Name:String;

  function IsDone(Ptr:NativeUInt):Boolean;
  Var I:Int32;
  begin
    for I:=Low(Done) to High(Done) do
      if Done[I]=Ptr then Exit(True);
    Result:=False;
  end;
begin
  Ptrs[0]:=Context.Ebx;
  Ptrs[1]:=Context.Esi;
  Ptrs[2]:=Context.Edi;
  Ptrs[3]:=Context.Eax;
  Ptrs[4]:=Context.Ecx;
  Ptrs[5]:=Context.Edx;
  Ptrs[6]:=Context.Ebp;
  if not ReadProcessMemory(PI.hProcess,Pointer(Context.Esp),@Ptrs[7],16*SizeOf(NativeUInt),BytesT) then
    FillChar(Ptrs[7],16*SizeOf(NativeUInt),0);
  Done:=nil;
  for I:=Low(Ptrs) to High(Ptrs) do
  begin
    if IsDone(Ptrs[I]) or not ReadLuaTable(Ptrs[I],T) then Continue;
    //Registers also show tables with a corrupted header, stack slots only plausible ones
    if (I>High(RegNames)) and not IsLuaTableHeaderValid(T) then Continue;
    Done:=Done+[Ptrs[I]];
    if I<=High(RegNames) then
      Name:=RegNames[I] else
      Name:='[ESP+0x'+UIntToHex((I-High(RegNames)-1)*SizeOf(NativeUInt),True)+']';
    AddEventReport(Reports,#13+'Lua table in '+Name+':'+#13+GetLuaTableDumpStr(Ptrs[I],T),'','');
  end;
end;

procedure FindStuff(var Reports:TArray<TEventReport>;const Context:TContext);
  procedure GetClass(SelfPtr:NativeUInt);
  Var Str:String;
  begin
    Str:=GetCObjectInfo(SelfPtr);
    if Str='' then Exit;
    AddEventReport(Reports,Str,'','');
  end;

  function GetLuaPt(lua_State:NativeUInt):Boolean;
  Var SType:Int32;
      Str:String;
  begin
    Result:=False;
    SType:=lStateType(lua_State);
    if SType<1 then Exit;
    if SType=1 then
      Str:='LUA Main thread' else Str:='LUA Fork thread';
    Str:=Str+#13+GetCallsReport(lua_State,Context.Esp);
    AddEventReport(Reports,'',Str,'');
    Result:=True;
  end;

Var Data:Array[1..50] of NativeUInt;
    BytesT:NativeUInt;
    I:Int32;
begin
  GetClass(Context.Edi);
  GetClass(Context.Esi);
  GetClass(Context.Ebx);
  GetClass(Context.Edx);
  GetClass(Context.Ecx);
  GetClass(Context.Eax);
  GetClass(Context.Ebp);
  GetClass(Context.Esp);

  GetLuaPt(Context.Edi);
  GetLuaPt(Context.Esi);
  GetLuaPt(Context.Ebx);
  GetLuaPt(Context.Edx);
  GetLuaPt(Context.Ecx);
  GetLuaPt(Context.Eax);
  GetLuaPt(Context.Ebp);
  GetLuaPt(Context.Esp);

  if not ReadProcessMemory(PI.hProcess,Pointer(Context.Esp),@Data,SizeOf(Data),BytesT) then Exit;
  for I:=Low(Data) to High(Data) do
    GetClass(Data[I]);
  for I:=Low(Data) to High(Data) do
    if GetLuaPt(Data[I]) then Break;
end;

//Watches up to 4 dwords with hardware write breakpoints. Lua requests a watch by raising an error
//inside pcall, which FA throws as a C++ exception:
//  pcall(error,"FADeepProbe watch <table address> <key> <key>...",0) watches the type tags of string keys
//  pcall(error,"FADeepProbe watchaddr <address>[+<offset>]...",0)   watches raw addresses
//Only Lua's table code (ltable.c) writes key type tags, so a key watch reports any other write.
//A raw address belongs to whatever uses that memory at the time. It becomes a key tag when ltable.c
//writes it with a table in a register whose node array holds it, and any other write while that table
//still owns the node array is reported. Other writers are counted for the report.
const
  WatchKeyMarker:UTF8String='FADeepProbe watch ';
  WatchAddrMarker:UTF8String='FADeepProbe watchaddr ';
  WatchPollMs=250;
  MaxWatchSlots=4; //Debug registers DR0-DR3
  MaxWatchReports=8;
  MaxWatchWriters=32;
  LuaStringTT=4;
  THREAD_SUSPEND_RESUME=$0002;
  CONTEXT_DEBUG_REGISTERS=$00010010;
  ERROR_SEM_TIMEOUT=121;

type
  TWatchSlot=record
    Addr:DWord;
    Armed:Boolean;    //False when unused or stopped
    Key:UTF8String;   //Watched key, '' for a raw address
    Table:NativeUInt; //Table whose node array holds Addr, 0 if none
    Node:DWord;       //Node array of Table when it was learned
    Value:DWord;      //Last value seen at Addr
    Hits,LuaWrites:UInt32;
  end;
  TWatchWriter=record
    Addr,Eip,Count,FirstTick,LastTick,Value:DWord;
  end;

var
  ThreadIds:TArray<DWord>;
  WatchReports:TArray<TEventReport>;
  Slots:Array[0..MaxWatchSlots-1] of TWatchSlot;
  Writers:TArray<TWatchWriter>;
  WatchTable:NativeUInt=0; //Table of the key watch, 0 for none
  WatchNode:DWord=0;       //Its node array when armed
  WatchKeys:TArray<UTF8String>;
  WatchReportCnt:Int32=0;
  LastWatchPoll:DWord=0;
  WatchRearm:Boolean=False;

function ReadGameTick:UInt32;
Var V,BytesT:NativeUInt;
begin
  Result:=GameTick;
  if ReadProcessMemory(PI.hProcess,Pointer($10A63F0),@V,SizeOf(V),BytesT) and (V>0)
  and ReadProcessMemory(PI.hProcess,Pointer(V+$900),@V,SizeOf(V),BytesT) then
    Result:=V;
end;

procedure ClearSlots;
Var I:Int32;
begin
  for I:=0 to MaxWatchSlots-1 do
    Slots[I]:=Default(TWatchSlot);
end;

function ReadDWord(Addr:NativeUInt;out V:DWord):Boolean;
Var BytesT:NativeUInt;
begin
  Result:=ReadProcessMemory(PI.hProcess,Pointer(Addr),@V,SizeOf(V),BytesT);
end;

function IsWatching:Boolean;
Var I:Int32;
begin
  for I:=0 to MaxWatchSlots-1 do
    if Slots[I].Armed then Exit(True);
  Result:=False;
end;

//Loads the slot addresses into DR0-DR3 of one thread, as 4 byte write breakpoints
procedure SetDebugRegs(ThreadId:DWord);
Var hThread:THandle;
    C:TContext;
    I:Int32;
begin
  hThread:=OpenThread(THREAD_GET_CONTEXT or THREAD_SET_CONTEXT or THREAD_SUSPEND_RESUME,False,ThreadId);
  if hThread=0 then Exit;
  SuspendThread(hThread);
  C.ContextFlags:=CONTEXT_DEBUG_REGISTERS;
  if GetThreadContext(hThread,C) then
  begin
    C.Dr0:=Slots[0].Addr;
    C.Dr1:=Slots[1].Addr;
    C.Dr2:=Slots[2].Addr;
    C.Dr3:=Slots[3].Addr;
    C.Dr7:=C.Dr7 and $FF00;
    for I:=0 to MaxWatchSlots-1 do
      if Slots[I].Armed then //Local enable, break on write, 4 bytes
        C.Dr7:=C.Dr7 or (DWord(1) shl (I*2)) or (DWord($D) shl (16+I*4));
    SetThreadContext(hThread,C);
  end;
  ResumeThread(hThread);
  CloseHandle(hThread);
end;

procedure SetAllDebugRegs;
Var I:Int32;
begin
  for I:=Low(ThreadIds) to High(ThreadIds) do
    SetDebugRegs(ThreadIds[I]);
end;

//True while the table that owned the slot's address still has the same node array
function IsSlotOwned(const S:TWatchSlot;out T:TLuaTable):Boolean;
begin
  Result:=(S.Table<>0) and ReadLuaTable(S.Table,T) and (T.Node=S.Node);
end;

//Finds a table in the registers whose node array has Addr as a key type tag
function FindKeyOwner(const C:TContext;Addr:DWord;out Table:NativeUInt;out Node:DWord):Boolean;
Var Ptrs:Array[0..6] of NativeUInt;
    T:TLuaTable;
    I:Int32;
begin
  Ptrs[0]:=C.Ebx;
  Ptrs[1]:=C.Esi;
  Ptrs[2]:=C.Edi;
  Ptrs[3]:=C.Eax;
  Ptrs[4]:=C.Ecx;
  Ptrs[5]:=C.Edx;
  Ptrs[6]:=C.Ebp;
  for I:=Low(Ptrs) to High(Ptrs) do
    if ReadLuaTable(Ptrs[I],T) and IsLuaTableHeaderValid(T) and (LuaNodeIndex(T,Addr)>=0) then
    begin
      Table:=Ptrs[I];
      Node:=T.Node;
      Exit(True);
    end;
  Result:=False;
end;

function SlotName(const S:TWatchSlot):String;
begin
  if S.Key<>'' then
    Result:='the type tag of key "'+S.Key+'"' else
    Result:='a key type tag of table 0x'+UIntToHex(S.Table);
end;

//Finds the watched keys in the node array of WatchTable and arms their type tags
procedure ArmKeyWatch;
Var T:TLuaTable;
    N:TLuaNode;
    BytesT:NativeUInt;
    I,K,Cnt:Int32;
    Str:String;
begin
  ClearSlots;
  WatchNode:=0;
  Str:='';
  if ReadLuaTable(WatchTable,T) and IsLuaTableHeaderValid(T) then
  begin
    WatchNode:=T.Node;
    Cnt:=1 shl T.LSizeNode;
    if Cnt>MaxDumpNodes then Cnt:=MaxDumpNodes;
    for I:=0 to Cnt-1 do
      if ReadProcessMemory(PI.hProcess,Pointer(T.Node+DWord(I)*LuaNodeSize),@N,SizeOf(N),BytesT)
      and (N.KeyTT=LuaStringTT) then
        for K:=Low(WatchKeys) to High(WatchKeys) do
          if not Slots[K].Armed and (ReadLuaStr(N.KeyV)=WatchKeys[K]) then
          begin
            Slots[K].Addr:=T.Node+DWord(I)*LuaNodeSize;
            Slots[K].Armed:=True;
            Slots[K].Key:=WatchKeys[K];
            Slots[K].Table:=WatchTable;
            Slots[K].Node:=T.Node;
            Slots[K].Value:=LuaStringTT;
            Str:=Str+' "'+WatchKeys[K]+'" ['+IntToStr(I)+']';
          end;
  end;
  if Str='' then Str:=' nothing';
  SetAllDebugRegs;
  DbgStrs:=DbgStrs+['Watch: table 0x'+UIntToHex(WatchTable)+', node 0x'+UIntToHex(WatchNode)
    +', tick '+IntToStr(ReadGameTick)+', armed'+Str];
end;

//Addresses are hex, optionally with a hex offset, such as 1A2B3C40+1C:
//Lua numbers are floats and can't hold an address
procedure ArmAddrWatch(const Addrs:TArray<UTF8String>);
Var I,P:Int32;
    Str,A:String;
begin
  ClearSlots;
  WatchTable:=0;
  Str:='';
  for I:=0 to Length(Addrs)-1 do
  begin
    if I>=MaxWatchSlots then Break;
    A:=String(Addrs[I]);
    P:=Pos('+',A);
    if P>0 then
      Slots[I].Addr:=(HexToUInt(Copy(A,1,P-1))+HexToUInt(Copy(A,P+1,MaxInt))) and not 3 else
      Slots[I].Addr:=HexToUInt(A) and not 3;
    Slots[I].Armed:=True;
    ReadDWord(Slots[I].Addr,Slots[I].Value);
    Str:=Str+' 0x'+UIntToHex(Slots[I].Addr);
  end;
  SetAllDebugRegs;
  DbgStrs:=DbgStrs+['Watch: tick '+IntToStr(ReadGameTick)+', armed addresses'+Str];
end;

//Arms a watch if the C++ exception is a Lua error carrying a watch request.
//FA throws Lua errors as lua_RuntimeError, which keeps its lua_State at +$2C,
//and the error message is on the top of that Lua stack.
function HandleWatchRequest(ErrorPtr:NativeUInt):Boolean;
Var BytesT,L,Top:NativeUInt;
    Obj:Array[0..1] of DWord;
    P:Int32;
    Msg:UTF8String;
    IsAddr:Boolean;
    Args:TArray<UTF8String>;
begin
  Result:=False;
  if not ReadProcessMemory(PI.hProcess,Pointer(ErrorPtr+$2C),@L,SizeOf(L),BytesT)
  or (lStateType(L)<1)
  or not ReadProcessMemory(PI.hProcess,Pointer(L+8),@Top,SizeOf(Top),BytesT)
  or not ReadProcessMemory(PI.hProcess,Pointer(Top-8),@Obj,SizeOf(Obj),BytesT)
  or (Obj[0]<>LuaStringTT) then Exit;
  //FA's _TRACEBACK rewrites the message, so find the request in it and stop at the end of its line
  Msg:=ReadLuaStr(Obj[1]);
  P:=Pos(WatchAddrMarker,Msg);
  IsAddr:=P>0;
  if IsAddr then
    Msg:=Copy(Msg,P+Length(WatchAddrMarker),MaxInt) else
  begin
    P:=Pos(WatchKeyMarker,Msg);
    if P=0 then Exit;
    Msg:=Copy(Msg,P+Length(WatchKeyMarker),MaxInt);
  end;
  Result:=True;
  P:=Pos(#10,Msg);
  if P>0 then Msg:=Copy(Msg,1,P-1);
  Args:=nil;
  while Msg<>'' do
  begin
    P:=Pos(' ',Msg);
    if P=0 then P:=Length(Msg)+1;
    if P>1 then Args:=Args+[Copy(Msg,1,P-1)];
    Msg:=Copy(Msg,P+1,MaxInt);
  end;
  if IsAddr then
  begin
    if Length(Args)>0 then
      ArmAddrWatch(Args);
  end else
  if Length(Args)>=2 then
  begin
    WatchTable:=HexToUInt(String(Args[0]));
    WatchKeys:=Copy(Args,1,MaxWatchSlots);
    ArmKeyWatch;
  end;
  //Resuming from the exception restores the debug registers of the raising thread, arm it again later
  WatchRearm:=True;
end;

procedure AddWriter(Addr,Eip,Value:DWord);
Var I:Int32;
    Tick:DWord;
begin
  Tick:=ReadGameTick;
  for I:=Low(Writers) to High(Writers) do
    if (Writers[I].Addr=Addr) and (Writers[I].Eip=Eip) then
    begin
      Inc(Writers[I].Count);
      Writers[I].LastTick:=Tick;
      Writers[I].Value:=Value;
      Exit;
    end;
  if Length(Writers)>=MaxWatchWriters then Exit;
  SetLength(Writers,Length(Writers)+1);
  Writers[High(Writers)].Addr:=Addr;
  Writers[High(Writers)].Eip:=Eip;
  Writers[High(Writers)].Count:=1;
  Writers[High(Writers)].FirstTick:=Tick;
  Writers[High(Writers)].LastTick:=Tick;
  Writers[High(Writers)].Value:=Value;
end;

//Reports a write to a slot's address from outside ltable.c while a table owns it
procedure ReportWatchWrite(var S:TWatchSlot;const T:TLuaTable;const C:TContext;ThreadId,V:DWord);
Var Str:String;
begin
  Inc(WatchReportCnt);
  Str:='Write to 0x'+UIntToHex(S.Addr)+', '+SlotName(S)+', 0x'+UIntToHex(S.Value)+' -> 0x'+UIntToHex(V)
    +#13+'Game tick: '+IntToStr(ReadGameTick)+', thread '+IntToStr(ThreadId)+', EIP is the instruction after the write'+#13
    +'EAX: 0x'+UIntToHex(C.Eax)+', EBX: 0x'+UIntToHex(C.Ebx)+', '
    +'ECX: 0x'+UIntToHex(C.Ecx)+', EDX: 0x'+UIntToHex(C.Edx)+#13
    +'ESI: 0x'+UIntToHex(C.Esi)+', EDI: 0x'+UIntToHex(C.Edi)+', '
    +'EBP: 0x'+UIntToHex(C.Ebp)+', ESP: 0x'+UIntToHex(C.Esp)+', EIP: 0x'+UIntToHex(C.Eip);
  AddEventReport(WatchReports,'',Str+#13,
    'Stacktrace:'+StacktraceToStr([PByte(C.Eip)]+StackWalk(PDWord(C.Esp),7))+#13#13
    +'MiniDump:'+#13+GetMiniDumpStr(Pointer(C.Eip))+#13#13
    +'Watched table:'+#13+GetLuaTableDumpStr(S.Table,T));
  FindStuff(WatchReports,C);
end;

//Handles a hardware breakpoint hit on a slot. False for other single steps.
function HandleWatchHit(ThreadId:DWord):Boolean;
Var hThread:THandle;
    C:TContext;
    T:TLuaTable;
    V:DWord;
    I:Int32;
    InLTable,Owned:Boolean;
begin
  Result:=False;
  hThread:=OpenThread(THREAD_GET_CONTEXT or THREAD_SET_CONTEXT,False,ThreadId);
  if hThread=0 then Exit;
  C.ContextFlags:=CONTEXT_CONTROL or CONTEXT_INTEGER or CONTEXT_DEBUG_REGISTERS;
  if GetThreadContext(hThread,C) and (C.Dr6 and $F<>0) then
  begin
    Result:=True;
    InLTable:=(C.Eip>=LTableCodeStart) and (C.Eip<LTableCodeEnd);
    for I:=0 to MaxWatchSlots-1 do
    with Slots[I] do
      if (C.Dr6 and (DWord(1) shl I)<>0) and Armed and ReadDWord(Addr,V) then
      begin
        Inc(Hits);
        if InLTable then
        begin
          Inc(LuaWrites);
          if (Key='') and not FindKeyOwner(C,Addr,Table,Node) then
            Table:=0;
        end else
        begin
          Owned:=IsSlotOwned(Slots[I],T);
          if Owned and (V<>Value) and (WatchReportCnt<MaxWatchReports) then
            ReportWatchWrite(Slots[I],T,C,ThreadId,V);
          if Key<>'' then
          begin
            if Owned and (V<>Value) then Armed:=False; //Reported, stop watching this key
          end else
          begin
            if not Owned or (V<>Value) then
              Table:=0; //No longer a key tag
            AddWriter(Addr,C.Eip,V);
          end;
        end;
        Value:=V;
      end;
    C.Dr6:=0;
    C.ContextFlags:=CONTEXT_DEBUG_REGISTERS;
    SetThreadContext(hThread,C);
    SetAllDebugRegs;
  end;
  CloseHandle(hThread);
end;

//Re-arms a key watch whose node array moved, drops owners that freed their node array, and reports
//key tags that changed without a reported write, such as writes from the kernel, which debug registers
//don't catch
procedure PollWatch;
Var T:TLuaTable;
    V:DWord;
    I:Int32;
begin
  LastWatchPoll:=GetTickCount;
  if WatchRearm then
  begin
    WatchRearm:=False;
    SetAllDebugRegs;
  end;
  if WatchTable<>0 then
    if not ReadLuaTable(WatchTable,T) then
    begin
      DbgStrs:=DbgStrs+['Watch: table 0x'+UIntToHex(WatchTable)+' is gone, tick '+IntToStr(ReadGameTick)];
      WatchTable:=0;
      ClearSlots;
      SetAllDebugRegs;
      Exit;
    end else
    if T.Node<>WatchNode then
    begin
      ArmKeyWatch;
      Exit;
    end;
  for I:=0 to MaxWatchSlots-1 do
  with Slots[I] do
    if Armed and (Table<>0) and ReadDWord(Addr,V) and (V<>Value) then
    begin
      if IsSlotOwned(Slots[I],T) and (WatchReportCnt<MaxWatchReports) then
      begin
        Inc(WatchReportCnt);
        AddEventReport(WatchReports,'','Value at 0x'+UIntToHex(Addr)+', '+SlotName(Slots[I])
          +', changed 0x'+UIntToHex(Value)+' -> 0x'+UIntToHex(V)+' without a reported write, found by polling at tick '
          +IntToStr(ReadGameTick)+#13,'Watched table:'+#13+GetLuaTableDumpStr(Table,T));
      end;
      if Key<>'' then
      begin
        Armed:=False;
        SetAllDebugRegs;
      end else
        Table:=0;
      Value:=V;
    end;
end;

//Hit counts and the writers outside ltable.c, for the report
function GetWatchSummaryStr:String;
Var I:Int32;
begin
  Result:='';
  for I:=0 to MaxWatchSlots-1 do
    if Slots[I].Hits>0 then
      Result:=Result+'0x'+UIntToHex(Slots[I].Addr)+': '+IntToStr(Slots[I].Hits)+' writes, '
        +IntToStr(Slots[I].LuaWrites)+' from ltable.c'+#13;
  for I:=Low(Writers) to High(Writers) do
  with Writers[I] do
    Result:=Result+'0x'+UIntToHex(Addr)+' written by'+StacktraceToStr([PByte(Eip)])+' x'+IntToStr(Count)
      +', ticks '+IntToStr(FirstTick)+'-'+IntToStr(LastTick)+', last value 0x'+UIntToHex(Value)+#13;
  if Length(Writers)>=MaxWatchWriters then
    Result:=Result+'Only the first '+IntToStr(MaxWatchWriters)+' writers are listed'+#13;
end;

procedure CPPExceptionHandling(SelfPtr:NativeUInt;const Context:TContext);
Var ClassName:String;
    Data:Array[1..50] of NativeUInt;
    BytesT:NativeUInt;
    I:Int32;

  function GetLuaPt(lua_State:NativeUInt):Boolean;
  Var SType:Int32;
      Pt:String;
  begin
    Result:=False;
    SType:=lStateType(lua_State);
    if SType<1 then Exit;
    if SType=1 then
      Pt:='LUA Main thread' else Pt:='LUA Fork thread';
    Pt:=Pt+#13+GetCallsReport(lua_State,Context.Esp);
    AddEventReport(CPPReports,ClassName,Pt,'');
    Result:=Pt<>'';
  end;
begin
  ClassName:=GetClassName(SelfPtr);
  if ClassName='' then Exit;
  if GetLuaPt(Context.Edi) then Exit;
  if GetLuaPt(Context.Esi) then Exit;
  if GetLuaPt(Context.Ebx) then Exit;
  if GetLuaPt(Context.Edx) then Exit;
  if GetLuaPt(Context.Ecx) then Exit;
  if GetLuaPt(Context.Eax) then Exit;
  if GetLuaPt(Context.Ebp) then Exit;
  if GetLuaPt(Context.Esp) then Exit;

  if not ReadProcessMemory(PI.hProcess,Pointer(Context.Esp),@Data,SizeOf(Data),BytesT) then Exit;
  for I:=Low(Data) to High(Data) do
    if GetLuaPt(Data[I]) then Exit;
end;

procedure WriteLog(const Str:UTF8String);
Var BytesT:Cardinal;
begin
  WriteFile(LogFile,Str[1],Length(Str),BytesT,nil);
end;

procedure WriteReports(const Reports:TArray<TEventReport>);
Var I,I2:Int32;
begin
  for I:=Low(Reports) to High(Reports) do
  with Reports[I] do
  begin
    if ClassName<>'' then
      WriteLog(Demangle(ClassName)+#13);
    for I2:=Low(EntryPts) to High(EntryPts) do
    begin
      WriteLog(EntryPts[I2].Pt+#13);
      WriteLog(EntryPts[I2].Prms+#13);
    end;
  end;
end;

procedure WriteReport;
Var I:Int32;
    hNtDll:HMODULE;
    WineGetVersion:TWineGetVersion;
    VI:TOSVersionInfoExW;
begin
  SetFilePointer(LogFile,0,nil,2);
  if GetFileSize(LogFile,nil)>0 then
    WriteLog(#13);

  WriteLog('Command line:'+#13);
  WriteLog(CmdLine+#13#13);

  hNtDll:=GetModuleHandleW('ntdll.dll');
  @WineGetVersion:=GetProcAddress(hNtDll,'wine_get_version');
  if Assigned(WineGetVersion) then
    WriteLog('Wine '+WineGetVersion()+#13);

  FillChar(VI,SizeOf(VI),0);
  VI.dwOSVersionInfoSize:=SizeOf(VI);
  RtlGetVersion(VI);
  WriteLog('Windows '+IntToStr(VI.dwMajorVersion)
    +'.'+IntToStr(VI.dwMinorVersion)
    +' (Build '+IntToStr(VI.dwBuildNumber)+')'+#13#13);

  WriteLog('Exit code: '+IntToStr(ExitCode)+#13);
  WriteLog('Engine ver.: '+IntToStr(GameVer)+#13);
  WriteLog('Game tick: '+IntToStr(GameTick)+#13);

  if MonitorReports<>nil then
  begin
    WriteLog(#13+'Monitor:'+#13);
    WriteReports(MonitorReports);
  end;

  if AVReports<>nil then
  begin
    WriteLog(#13);
    WriteReports(AVReports);
  end;

  if CPPReports<>nil then
  begin
    WriteLog(#13+'C++ Exceptions:'+#13);
    WriteReports(CPPReports);
  end;

  Str:=GetWatchSummaryStr;
  if (WatchReports<>nil) or (Str<>'') then
  begin
    WriteLog(#13+'Watch:'+#13);
    WriteLog(Str);
    WriteReports(WatchReports);
  end;

  if DbgStrs<>nil then
  begin
    WriteLog(#13+'Debug messages:'+#13);
    for I:=Low(DbgStrs) to High(DbgStrs) do
      WriteLog(DbgStrs[I]+#13);
  end;

  if (MonitorReports<>nil) or (AVReports<>nil) or (CPPReports<>nil) or (WatchReports<>nil) then
  begin
    WriteLog(#13+'DLLs:');
    for I:=Low(DLLs) to High(DLLs) do
      WriteLog(DLLs[I]+#13);
  end;
end;

function CloseConsole(dwCtrlType:Cardinal):LongBool;stdcall;
begin
  Result:=False;
  case dwCtrlType of
    CTRL_CLOSE_EVENT,CTRL_LOGOFF_EVENT,CTRL_SHUTDOWN_EVENT:
      WriteReport;
  end;
end;

function GetCommandLineArg(Key:String;DeleteArg:Boolean):String;
Var I,I2:Int32;
begin
  Result:='';
  I:=Pos(Key,CmdLine);
  if I>0 then
  begin
    I:=I+Length(Key);
    I2:=Pos('/',CmdLine,I)-1;
    if I2<I then I2:=Length(CmdLine)+1;
    Result:=Copy(CmdLine,I,I2-I);
    if DeleteArg then
      CmdLine:=Copy(CmdLine,1,I-5)+Copy(CmdLine,I2);
  end;
end;

begin
  CmdLine:=GetCommandLineW;
  I:=Pos(ParamStr(1),CmdLine);
  if I<1 then CmdLine:='' else
    if CmdLine[I-1]='"' then
      CmdLine:=Copy(CmdLine,I-1) else
      CmdLine:=Copy(CmdLine,I);

  WorkDir:=GetFilePath(ParamStr(1));
  if WorkDir='' then
    WorkDir:=GetFilePath(CmdLine);
  if WorkDir='' then
  begin
    WorkDir:=GetFilePath(ParamStr(0));
    if (CmdLine='') or (Pos('/',CmdLine)=1) then
    begin
      if (CmdLine<>'') and (CmdLine[1]<>' ') then
        CmdLine:=' '+CmdLine;
      if FileExists('ForgedAlliance.exe') then
        CmdLine:='ForgedAlliance.exe'+CmdLine else
        CmdLine:=GetEnvVar('ProgramData')+'\FAForever\bin\ForgedAlliance.exe'+CmdLine;
    end;
  end;

  ProfilePtr:=HexToUInt(GetCommandLineArg('/p ',True));

  Str:=GetCommandLineArg('/log ',False);
  if (Str<>'') and (Str[1]='"') then
    Str:=Copy(Str,2,Length(Str)-2);
  if Str='' then
    Str:='Report.txt' else
  if GetFilePath(Str)='' then
    Str:=WorkDir+Str;
  LogFile:=CreateFileW(PChar(Str),GENERIC_WRITE,FILE_SHARE_READ or FILE_SHARE_WRITE,nil,CREATE_ALWAYS,FILE_ATTRIBUTE_NORMAL,0);
  if (LogFile=0) or (LogFile=$FFFFFFFF) then
  begin
    MessageBoxW(0,PChar('CreateFileW->'+#13+Str),'Error',MB_ICONERROR);
    Halt;
  end;

  FillChar(SI,SizeOf(SI),0);
  FillChar(PI,SizeOf(PI),0);
  SI.cb:=SizeOf(SI);
  if not CreateProcessW(nil,PChar(CmdLine),nil,nil,False,
    DEBUG_ONLY_THIS_PROCESS,nil,PChar(WorkDir),SI,PI) then
  begin
    MessageBoxW(0,PChar('CreateProcessW->'+#13+CmdLine),'Error',MB_ICONERROR);
    Halt;
  end;

  SetConsoleCtrlHandler(@CloseConsole,True);
  while DbgActive do
  begin
    if GetTickCount-LastWatchPoll>=WatchPollMs then
      PollWatch;
    if not WaitForDebugEvent(DbgEvent,WatchPollMs) then
      if GetLastError=ERROR_SEM_TIMEOUT then Continue else Break;
    case DbgEvent.dwDebugEventCode of
      EXCEPTION_DEBUG_EVENT: begin
        with DbgEvent.Exception.ExceptionRecord do
        case ExceptionCode of
          EXCEPTION_BREAKPOINT: begin
            if BPExceptionHandling(ExceptionAddress,ExceptionBP) then
            begin
              hThread:=OpenThread(THREAD_GET_CONTEXT or THREAD_SET_CONTEXT,False,DbgEvent.dwThreadId);
              Context.ContextFlags:=CONTEXT_CONTROL or CONTEXT_INTEGER;
              GetThreadContext(hThread,Context);

              Inc(EventsCnt);
              FindStuff(MonitorReports,Context);
              SetConsoleTitleW(PChar('Events: '+IntToStr(EventsCnt)+'  Classes: '
                +IntToStr(Length(MonitorReports))));

              Context.EFlags:=Context.EFlags or $100; //Set EXCEPTION_SINGLE_STEP
              Context.Eip:=DWord(ExceptionAddress);
              SetThreadContext(hThread,Context);
              CloseHandle(hThread);
              ContinueDebugEvent(DbgEvent.dwProcessId,DbgEvent.dwThreadId,DBG_CONTINUE);
              Continue;
            end;
          end;
          EXCEPTION_SINGLE_STEP: begin
            if HandleWatchHit(DbgEvent.dwThreadId) then
            begin
              ContinueDebugEvent(DbgEvent.dwProcessId,DbgEvent.dwThreadId,DBG_CONTINUE);
              Continue;
            end;
            for I:=Low(SoftBPs) to High(SoftBPs) do
              if not(BPSActive in SoftBPs[I].State) then
                SoftBPs[I].Enable;
            ContinueDebugEvent(DbgEvent.dwProcessId,DbgEvent.dwThreadId,DBG_CONTINUE);
            Continue;
          end;
          EXCEPTION_ACCESS_VIOLATION: begin
            ExitCode:=1;
            hThread:=OpenThread(THREAD_GET_CONTEXT or THREAD_SET_CONTEXT,False,DbgEvent.dwThreadId);
            Context.ContextFlags:=CONTEXT_CONTROL or CONTEXT_INTEGER;
            GetThreadContext(hThread,Context);

            GameTick:=ReadGameTick;
            if ExceptionInformation[0]=0 then
              Str:='ACCESS_VIOLATION: Read from 0x'+UIntToHex(ExceptionInformation[1]) else
            if ExceptionInformation[0]=1 then
              Str:='ACCESS_VIOLATION: Write to 0x'+UIntToHex(ExceptionInformation[1]) else
              Str:='ACCESS_VIOLATION: Execute at 0x'+UIntToHex(ExceptionInformation[1]);
            if ExceptionAddress=Pointer($95854F) then
              Str:=Str+'  Out of memory/Alloc error';
            Str:=Str+#13
              +'EAX: 0x'+UIntToHex(Context.Eax)+', EBX: 0x'+UIntToHex(Context.Ebx)+', '
              +'ECX: 0x'+UIntToHex(Context.Ecx)+', EDX: 0x'+UIntToHex(Context.Edx)+#13
              +'ESI: 0x'+UIntToHex(Context.Esi)+', EDI: 0x'+UIntToHex(Context.Edi)+', '
              +'EBP: 0x'+UIntToHex(Context.Ebp)+', ESP: 0x'+UIntToHex(Context.Esp);
            AddEventReport(AVReports,'',Str+#13,'Stacktrace:'+StacktraceToStr([ExceptionAddress]+StackWalk(PDWord(Context.Esp),7)));
            FindStuff(AVReports,Context);
            Str:=GetMiniDumpStr(ExceptionAddress);
            if Str<>'' then
              AddEventReport(AVReports,#13+'MiniDump:'+#13+Str,'','');
            if (NativeUInt(ExceptionAddress)>=LTableCodeStart)
            and (NativeUInt(ExceptionAddress)<LTableCodeEnd) then
              DumpLuaTables(AVReports,Context);
            DbgActive:=False;

            CloseHandle(hThread);
            Continue;
          end;
          $E06D7363: begin //C++ exception
            hThread:=OpenThread(THREAD_GET_CONTEXT,False,DbgEvent.dwThreadId);
            Context.ContextFlags:=CONTEXT_CONTROL or CONTEXT_INTEGER;
            GetThreadContext(hThread,Context);
            CloseHandle(hThread);

            if not HandleWatchRequest(ExceptionInformation[1]) then
              CPPExceptionHandling(ExceptionInformation[1],Context);
          end;
        else
          hThread:=OpenThread(THREAD_GET_CONTEXT,False,DbgEvent.dwThreadId);
          Context.ContextFlags:=CONTEXT_CONTROL;
          GetThreadContext(hThread,Context);
          CloseHandle(hThread);

          Str:='EXCEPTION: Code '+UIntToHex(ExceptionCode)+#13+
            '  Stacktrace:'+StacktraceToStr([ExceptionAddress]+StackWalk(PDWord(Context.Esp),7));
          if FindStr(DbgStrs,Str)<0 then
            DbgStrs:=DbgStrs+[Str];
        end;
      end;
      CREATE_PROCESS_DEBUG_EVENT: begin
        ThreadIds:=ThreadIds+[DbgEvent.dwThreadId];
        ReadProcessMemory(PI.hProcess,Pointer($876666),@GameVer,SizeOf(GameVer),BytesT);
        if ProfilePtr>0 then
        begin
          AddSoftBP(Pointer(ProfilePtr),0,[BPSActive]);
          AddEventReport(MonitorReports,'Profiling: 0x'+UIntToHex(ProfilePtr),'','');
        end;
      end;
      EXIT_PROCESS_DEBUG_EVENT: begin
        ExitCode:=DbgEvent.ExitProcess.dwExitCode;
        DbgActive:=False;
      end;
      LOAD_DLL_DEBUG_EVENT: begin
        Str:=ReadDllName(DbgEvent.LoadDll);
        DLLs:=DLLs+[Str];
      end;
      CREATE_THREAD_DEBUG_EVENT: begin
        ThreadIds:=ThreadIds+[DbgEvent.dwThreadId];
        if IsWatching then
          SetDebugRegs(DbgEvent.dwThreadId);
      end;
      EXIT_THREAD_DEBUG_EVENT: begin
        for I:=High(ThreadIds) downto Low(ThreadIds) do
          if ThreadIds[I]=DbgEvent.dwThreadId then
            Delete(ThreadIds,I,1);
        if DbgEvent.ExitThread.dwExitCode<>0 then
          DbgStrs:=DbgStrs+['EXIT_THREAD: '+IntToStr(DbgEvent.ExitThread.dwExitCode)];
      end;
      OUTPUT_DEBUG_STRING_EVENT: begin
        DbgStrs:=DbgStrs+[ReadDebugString(DbgEvent.DebugString)];
      end;
    end;
    ContinueDebugEvent(DbgEvent.dwProcessId,DbgEvent.dwThreadId,DBG_EXCEPTION_NOT_HANDLED);
  end;
  if DbgActive then
    MessageBoxW(0,'WaitForDebugEvent','Error',MB_ICONERROR);
  WriteReport;
end.
