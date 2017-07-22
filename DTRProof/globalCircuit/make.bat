set @coq=C:\Coq85\bin\coqc.exe
echo ControlBlock compilation start:
%@coq% globalInv
%@coq% globalStep
%@coq% globalSeqs
%@coq% globalLem0
%@coq% globalLem1
%@coq% globalStepg0
%@coq% globalStepg1
%@coq% globalLib
echo DONE