set @coq=C:\Coq85\bin\coqc.exe
echo Transf compilation starts:
%@coq% dtrTransform
%@coq% relationPred
echo DONE