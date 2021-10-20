program FADeepProbe;

{$WEAKLINKRTTI ON}
{$RTTI EXPLICIT METHODS([]) FIELDS([]) PROPERTIES([])}

{$SetPEFlags $0001}
{$SetPEFlags $0002}
{$SetPEFlags $0004}
{$SetPEFlags $0008}
{$SetPEFlags $0010}
{$SetPEFlags $0200}

uses Winapi.Windows;

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

var
  CmdLine,WorkDir,Str:String;
  SI:TStartupInfo;
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
  GameVer,BytesT,V:NativeUInt;

const
  THREAD_GET_CONTEXT=$0008;
  THREAD_SET_CONTEXT=$0010;

function OpenThread(dwDesiredAccess:DWord;bInheritHandle:Boolean;dwThreadId:DWORD):DWORD;stdcall;external 'kernel32.dll';
function K32EnumProcessModules(hProcess:THandle;lphModule:PHMODULE;cb:DWORD;var lpcbNeeded:DWORD):BOOL;stdcall;external 'kernel32.dll';
function K32GetModuleInformation(hProcess:THandle;hModule:HMODULE;lpmodinfo:LPMODULEINFO;cb:DWORD):BOOL;stdcall;external 'kernel32.dll';
function K32GetModuleBaseNameW(hProcess:THandle;hModule:HMODULE;lpBaseName:LPCWSTR;nSize:DWORD):DWORD;stdcall;external 'kernel32.dll';

function GetEnvVar(const Name:String):String;
Var Size:UInt32;
begin
  Size:=GetEnvironmentVariable(PChar(Name),nil,0);
  SetLength(Result,Size-1);
  GetEnvironmentVariable(PChar(Name),PChar(Result),Size);
end;

function FileExists(const FileName:String):Boolean;
Var Data:TWin32FindData;
    hFile:THandle;
begin
  Result:=False;
  hFile:=FindFirstFile(PChar(FileName),Data);
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

function HexToUInt(Str:String):NativeUInt;
Var I:Integer;
    C:NativeUInt;
begin
  Result:=0;
  for I:=1 to Length(Str) do
  begin
    Str[I]:=CharUpper(Str[I]);
    if (Str[I]>='0') and (Str[I]<='9') then
      C:=Ord(Str[I])-Ord('0') else
    if (Str[I]>='A') and (Str[I]<='F') then
      C:=Ord(Str[I])-Ord('A')+10 else Continue;
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

function TBreakpoint.Enable:Boolean;
Var Data:Byte;
    BytesT:NativeUInt;
begin
  Result:=False;
  Data:=$CC;
  WriteProcessMemory(PI.hProcess,Ptr,@Data,1,BytesT);
  if BytesT<>1 then
  begin
    MessageBox(0,'TBreakpoint.Enable->WriteProcessMemory','Error',MB_ICONERROR);
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
    MessageBox(0,'TBreakpoint.Disable->WriteProcessMemory','Error',MB_ICONERROR);
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
    MessageBox(0,'AddSoftBP->ReadProcessMemory','Error',MB_ICONERROR);
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
    for I:=Low(Data) to High(Data) do
      if Data[I]=#0 then Break;
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

function Verify_lua_State(lua_State:NativeUInt):Boolean;
Var BytesT,V:NativeUInt;
begin
  Result:=False;
  if not ReadProcessMemory(PI.hProcess,Pointer(lua_State+$44),@V,SizeOf(V),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(V),@V,SizeOf(V),BytesT) then Exit;
  Result:=lua_State=V;
end;

function GetLuaCallStr(lua_State,Lvl:NativeUInt):String;
Var BytesT,Base,Base2,Ptr,V:NativeUInt;
begin
  Result:='';
  if not ReadProcessMemory(PI.hProcess,Pointer(lua_State+$28),@Base,SizeOf(Base),BytesT) then Exit;
  Base:=Base+Lvl*5*8;

  if not ReadProcessMemory(PI.hProcess,Pointer(Base),@Base2,SizeOf(Base2),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(Base2-$4),@Base2,SizeOf(Base2),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(Base2+$18),@Base2,SizeOf(Base2),BytesT) then Exit;

  if not ReadProcessMemory(PI.hProcess,Pointer(Base2+$20),@Ptr,SizeOf(Ptr),BytesT) then Exit;
  Result:=ReadLuaStr(Ptr);
  if (Result='') or (Result[1]<>'@') then Exit;

  if not ReadProcessMemory(PI.hProcess,Pointer(Base+$C),@Ptr,SizeOf(Ptr),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(Base2+$C),@Base,SizeOf(Base),BytesT) then Exit;
  Ptr:=Ptr-Base;
  if not ReadProcessMemory(PI.hProcess,Pointer(Base2+$14),@Base,SizeOf(Base),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(Ptr+Base),@V,SizeOf(V),BytesT) then Exit;
  Result:=Result+' '+IntToStr(V);
end;

function GetLuaFuncPtStr(FuncPtr:NativeUInt):String;
Var BytesT,Ptr,V:NativeUInt;
begin
  Result:='';
  if not ReadProcessMemory(PI.hProcess,Pointer(FuncPtr+$18),@FuncPtr,SizeOf(FuncPtr),BytesT) then Exit;

  if not ReadProcessMemory(PI.hProcess,Pointer(FuncPtr+$20),@Ptr,SizeOf(Ptr),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(Ptr+$14),@V,SizeOf(V),BytesT) then Exit;
  if Byte(V)<>$40 then Exit;
  Result:=ReadLuaStr(Ptr);

  if not ReadProcessMemory(PI.hProcess,Pointer(FuncPtr+$3C),@V,SizeOf(V),BytesT) then Exit;
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
begin
  Result:=GetClassName(SelfPtr);
  if Result='' then Exit;
  Result:=Demangle(Result);
  V:=GetTrueCObjectPtr(SelfPtr);
  A:=[$F6B810,$F8C018];
  I:=FindAncestor(V,A);
  case I of
    0: SelfPtr:=SelfPtr+$68;
    1: SelfPtr:=V+$44;
  else
    Exit;
  end;
  if not ReadProcessMemory(PI.hProcess,Pointer(SelfPtr),@V,SizeOf(V),BytesT) then Exit;
  Result:=Result+' ID:'+IntToStr(V);
  if not ReadProcessMemory(PI.hProcess,Pointer(SelfPtr+$4),@V,SizeOf(V),BytesT) then Exit;
  if V=0 then
  begin
    Result:=Result+' BpName:None';
    Exit;
  end;
  Str:=ReadFAStr(V+$8);
  if Str='' then
    Result:=Result+' BpName:Wrong' else
    Result:=Result+' BpName:'+Str;
end;

function GetLuaCallPrmsStr(lua_State:NativeUInt):String;
Var BytesT,S,E,T,V:NativeUInt;
begin
  Result:='';
  if not ReadProcessMemory(PI.hProcess,Pointer(lua_State+$8),@E,SizeOf(E),BytesT) then Exit;
  if not ReadProcessMemory(PI.hProcess,Pointer(lua_State+$C),@S,SizeOf(S),BytesT) then Exit;
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
      2: Result:=Result+'LightUserData:'+UIntToHex(V);
      3: Result:=Result+'Float:'+FloatToStr(PSingle(@V)^,6);
      4: Result:=Result+'String:'+ReadLuaStr(V);
      5: begin
        T:=Get_c_object(V);
        if T>0 then
          Result:=Result+'CObject:'+GetCObjectInfo(T) else
          Result:=Result+'Table'; //:'+UIntToHex(V);
      end;
      6: Result:=Result+'cFunction'; //:'+UIntToHex(V);
      7: Result:=Result+'Function:'+GetLuaFuncPtStr(V);
      8: Result:=Result+'UserData:'+UIntToHex(V);
      9: Result:=Result+'Thread'; //:'+UIntToHex(V);
    else
      Exit;
    end;
    S:=S+8;
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
  for I:=I to High(Data) do
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
  for I:=I to High(Reports) do
    if Reports[I].ClassName=ClassName then
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

procedure FindStuff(var Reports:TArray<TEventReport>;const Context:TContext);
  procedure GetClass(SelfPtr:NativeUInt);
  Var Str:String;
  begin
    Str:=GetClassName(SelfPtr);
    if Str='' then Exit;
    AddEventReport(Reports,Str,'','');
  end;

  function GetLuaPt(lua_State:NativeUInt):Boolean;
  Var Str:String;
  begin
    Result:=False;
    if not Verify_lua_State(lua_State) then Exit;
    Str:=GetLuaCallStr(lua_State,1);
    if Str='' then Exit;
    AddEventReport(Reports,'',Str,GetLuaCallPrmsStr(lua_State));
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

procedure CPPExceptionHandling(SelfPtr:NativeUInt;const Context:TContext);
Var ClassName:String;
    Data:Array[1..50] of NativeUInt;
    BytesT:NativeUInt;
    I:Int32;

  function GetLuaPt(lua_State:NativeUInt):Boolean;
  Var Pt,Prms:String;
  begin
    Result:=False;
    if not Verify_lua_State(lua_State) then Exit;
    Pt:=GetLuaCallStr(lua_State,1);
    if Pt='' then Prms:='' else
      Prms:=GetLuaCallPrmsStr(lua_State);
    AddEventReport(CPPReports,ClassName,Pt,Prms);
    Result:=(Pt<>'') or (Prms<>'');
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
begin
  SetFilePointer(LogFile,0,nil,2);
  if GetFileSize(LogFile,nil)>0 then
    WriteLog(#13);

  WriteLog('Command line:'+#13);
  WriteLog(CmdLine+#13#13);

  WriteLog('Exit code: '+IntToStr(ExitCode)+#13);
  WriteLog('Game version: '+IntToStr(GameVer)+#13);
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

  if DbgStrs<>nil then
  begin
    WriteLog(#13+'Debug messages:'+#13);
    for I:=Low(DbgStrs) to High(DbgStrs) do
      WriteLog(DbgStrs[I]+#13);
  end;

  WriteLog(#13+'DLLs:');
  for I:=Low(DLLs) to High(DLLs) do
    WriteLog(DLLs[I]+#13);
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
  CmdLine:=GetCommandLine;

  I:=1;
  for I:=I to Length(CmdLine) do
    if CmdLine[I]<=#32 then Break;
  for I:=I+1 to Length(CmdLine) do
    if CmdLine[I]>#32 then Break;
  if I=Length(CmdLine) then CmdLine:='' else
    CmdLine:=Copy(CmdLine,I);

  WorkDir:=GetFilePath(Copy(CmdLine,1,Pos(' ',CmdLine)));
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
  if Str='' then
    Str:='Report.txt' else
  if GetFilePath(Str)='' then
    Str:=WorkDir+Str;
  LogFile:=CreateFile(PChar(Str),GENERIC_WRITE,FILE_SHARE_READ or FILE_SHARE_WRITE,nil,CREATE_ALWAYS,FILE_ATTRIBUTE_NORMAL,0);

  FillChar(SI,SizeOf(SI),0);
  FillChar(PI,SizeOf(PI),0);
  SI.cb:=SizeOf(SI);
  if not CreateProcess(nil,PChar(CmdLine),nil,nil,False,
    DEBUG_ONLY_THIS_PROCESS,nil,PChar(WorkDir),SI,PI) then
  begin
    MessageBox(0,PChar('CreateProcess->'+#13+CmdLine),'Error',MB_ICONERROR);
    Halt;
  end;

  SetConsoleCtrlHandler(@CloseConsole,True);
  while DbgActive and WaitForDebugEvent(DbgEvent,INFINITE) do
  begin
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
              SetConsoleTitle(PChar('Events: '+IntToStr(EventsCnt)+'  Classes: '
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

            if (ReadProcessMemory(PI.hProcess,Pointer($10A63F0),@V,SizeOf(V),BytesT)) and (V>0) then
              if ReadProcessMemory(PI.hProcess,Pointer(V+$900),@V,SizeOf(V),BytesT) then GameTick:=V;
            if ExceptionInformation[0]=0 then
              Str:='ACCESS_VIOLATION: Read from 0x'+UIntToHex(ExceptionInformation[1]) else
              Str:='ACCESS_VIOLATION: Write to 0x'+UIntToHex(ExceptionInformation[1]);
            AddEventReport(AVReports,'',Str,'Stacktrace:'+StacktraceToStr([ExceptionAddress]+StackWalk(PDWord(Context.Esp),7)));
            FindStuff(AVReports,Context);
            Str:=GetMiniDumpStr(ExceptionAddress);
            if Str<>'' then
              AddEventReport(AVReports,'MiniDump:'+#13+Str,'','');
            DbgActive:=False;

            CloseHandle(hThread);
            Continue;
          end;
          $E06D7363: begin //C++ exception
            hThread:=OpenThread(THREAD_GET_CONTEXT,False,DbgEvent.dwThreadId);
            Context.ContextFlags:=CONTEXT_CONTROL or CONTEXT_INTEGER;
            GetThreadContext(hThread,Context);
            CloseHandle(hThread);

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
      EXIT_THREAD_DEBUG_EVENT: begin
        if DbgEvent.ExitThread.dwExitCode<>0 then
          DbgStrs:=DbgStrs+['EXIT_THREAD: '+IntToStr(DbgEvent.ExitThread.dwExitCode)];
      end;
      OUTPUT_DEBUG_STRING_EVENT: begin
        DbgStrs:=DbgStrs+[DbgEvent.DebugString.lpDebugStringData];
      end;
    end;
    ContinueDebugEvent(DbgEvent.dwProcessId,DbgEvent.dwThreadId,DBG_EXCEPTION_NOT_HANDLED);
  end;
  if DbgActive then
    MessageBox(0,'WaitForDebugEvent','Error',MB_ICONERROR);
  WriteReport;
end.
