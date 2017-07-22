@ECHO ControlBlock compilation start:
coqtop -compile controlFsmStep
coqtop -compile votersStepg
coqtop -compile controlRec
coqtop -compile controlStep0
coqtop -compile controlStep1
coqtop -compile controlStepg0
coqtop -compile controlStepg1
coqtop -compile controlLib
@ECHO DONE