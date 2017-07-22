set @coq=C:\Coq85\bin\coqc.exe
echo Common compilation start:
%@coq% LibTactics
%@coq% Utils
%@coq% Signals
%@coq% Syntax
%@coq% Semantics
%@coq% PropSem
%@coq% CirTactics
%@coq% PropSub
REM %@coq% -Q ``Z:\Work\CoqProofs\LDDL_8.5'' LDDL CirReflect
echo Common DONE