set @coq=C:\Coq85\bin\coqc.exe
echo ControlBlock compilation start:
%@coq% ttrDef
%@coq% ttrCMBlocks
%@coq% ttrInv
%@coq% ttrStep
%@coq% ttrStepg
%@coq% ttrMainTh
echo TTR DONE