set @coq=C:\Coq85\bin\coqc.exe
echo TMR compilation start:
%@coq% tmrDef
%@coq% tmrPlugs
%@coq% tmrMainTh
echo TMR DONE