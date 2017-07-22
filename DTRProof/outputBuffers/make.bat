set @coq=C:\Coq85\bin\coqc.exe
echo ControlBlock compilation start:
%@coq% outputStep
%@coq% outputStep0
%@coq% outputStep1
%@coq% outputRec
%@coq% outputStepg
%@coq% outputLib
echo DONE