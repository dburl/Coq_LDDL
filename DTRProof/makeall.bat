set @coq=C:\Coq85\bin\coqc.exe
echo DTR project compilation starts:
echo Transformation compilation:
cd Transf
CALL make.bat
cd ..
echo Sub-circuits compilation:
cd memoryBlocks
CALL make.bat 
cd ..
cd controlBlock
CALL make.bat
cd ..
cd inputBuffers
CALL make.bat
cd ..
cd outputBuffers
CALL make.bat
cd ..
cd globalCircuit
CALL make.bat
cd ..
%@coq% mainTheorem
echo DTR DONE