set @coq=C:\Coq85\bin\coqc.exe
echo MemoryBlock compilation start:
%@coq% leftStep
%@coq% leftStepg
%@coq% relationProp
%@coq% rightStep
%@coq% rightStepg
%@coq% memoryInv0
%@coq% memoryInv1
%@coq% memoryStep
%@coq% memoryStepg0
%@coq% memoryStepg1
%@coq% memoryRec
%@coq% memoryLib
echo DONE