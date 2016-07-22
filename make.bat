@ECHO OFF
REM Build the Oberon-0 compiler

REM .pas to get syntax highlighting, .m for Oxford to work
copy /Y OSS.pas OSS.m
copy /Y OSP.pas OSP.m
copy /Y OSG.pas OSG.m
copy /Y Test.pas Test.m

REM delete old execuable
del OSP.exe

REM Build the executable
obc OSS.m OSG.m OSP.m -o OSP.exe

REM Run the debugger
obdb OSP.exe Test.m