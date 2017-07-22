(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-  ctr block properties during even(1) cycles

          Dmitry Burlyaev - Pascal Fradet - 2015          
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)
(* Add LoadPath "..\..\Common\".
Require Import CirReflect . 
Add LoadPath "..\..\TMRProof\".
Require Import tmrMainTh.
Add LoadPath "..\".
Require Import dtrTransform.
Add LoadPath "..\memoryBlocks".
*)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".
Add LoadPath "..\memoryBlocks\".

Require Import dtrTransform controlFsmStep.

Set Implicit Arguments.

(* ########################################################## *)
(** Properties of DTR control block during the even(1) cycles  *)
(* ########################################################## *)

(*Normal mode: from the state '001' the control block goes to the states '000' if no fail signal raised*)
(*No glitches*)
Lemma step1_tcbv : forall  t c, step (ctrBlockTMR false false true)  {~0,~0,~0}  t c 
                                  -> t={~1,~0,~0,~0,~0} /\ c=(ctrBlockTMR false false false).
Proof.
introv H.
assert ( step (ctrBl_dtr false false true)   (~0)  {~1,~0,~0,~0,~0}(ctrBl_dtr false false false)). (*property of a single ctrBl*)
 - assert ( exists t, exists c', step (ctrBl_dtr false false true) (~0) t c' ). apply step_all_ex.
   Simpl. assert (HA :=  H0). apply fact_stepCtrBl_21 in H0. destruct H0; Simpl.
 - apply tmr_normal in H0. apply tmrVotRelat in H0.
   + Rdet. Simpl. 
   + Checkpure.
   + Checkpure.
Qed.

(*Error detection: from the state '001' the control block goes to the states '010' if the fail signal raised*)
(*No glitches*)
Lemma stepr1_tcbv : forall t c, step (ctrBlockTMR false false true)  {~1,~1,~1}  t c 
                          -> t={~1,~1,~1,~1,~1} /\ c=(ctrBlockTMR false true false).
Proof.
introv H.
assert ( step (ctrBl_dtr false false true)   (~1)  {~1,~1,~1,~1,~1}(ctrBl_dtr false true false)). (*property of a single ctrBl*)
- assert ( exists t, exists c', step (ctrBl_dtr false false true) (~1) t c' ). apply step_all_ex.
  Simpl. assert (HA :=  H0). apply fact_stepCtrBl_23 in H0. destruct H0; Simpl.
- apply tmr_normal in H0. apply tmrVotRelat in H0.
   + Rdet. Simpl. 
   + Checkpure.
   + Checkpure.
Qed.

(*Recovery from internal control block corruption during during the normal mode:
if one of three redundant parts of the control block is corrupted then 
the error disappears the next clock cycle thanks to TMR (without starting recovery since fail=0)*)
Lemma step1_tcbv_C: forall  t ctrTMR c, corrupt_1in3_cir (ctrBl_dtr false false true) ctrTMR 
                     ->  step (ctrTMR -o- ctrVoting)   {~0,~0,~0}  t  c 
                     -> t={~1,~0,~0,~0,~0} /\ c=(ctrBlockTMR false false false).
Proof.
introv H H0. unfold ctrBlockTMR.
apply tmr_corruptc  with (c':=(ctrBl_dtr false false false)) (s:=(~0)) (t:={~1,~0,~0,~0,~0}) in H.
 - Inverts H0. apply det_step with (c1:=c1') (t1:=t0 )  in H. Inverts H.
   + assert (F:  fstep ctrVoting {~ 1, ~ 0, ~ 0, ~ 0, ~ 0, 
                                 {~ 1, ~ 0, ~ 0, ~ 0, ~ 0},
                                 {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}}  = 
             Some ({~1,~0,~0,~0,~0} ,  ctrVoting)) by
     (vm_compute; try easy). eapply fstep_imp_detstep in F; Simpl.
   + Checkpure.
   + apply H5.
 - Checkpure.
 - assert ( exists t, exists c', step (ctrBl_dtr false false true) (~0) t c' ). apply step_all_ex.
  Simpl. assert (HA :=  H1). apply fact_stepCtrBl_21 in H1. destruct H1; Simpl.
Qed.