echo Coq project compilation start:
echo Sub-folders compilation:
cd Common
CALL make.bat 
cd ..
cd TMRProof
CALL make.bat
cd ..
cd DTRProof
CALL makeall.bat
cd ..
cd TTRProof
CALL make.bat
cd ..
echo ALL DONE