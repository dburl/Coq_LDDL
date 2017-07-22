(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation
#</h1>#
-  ctr block properties during even(1) cycles with a glitch

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

Require Import dtrTransform controlFsmStep votersStepg.

Set Implicit Arguments.

(* ####################################################################### *)
(** Properties of DTR control block during a even(1) cycles  with a GLITCH *)
(* ####################################################################### *)

(*If a glitch happens then only one redudant copy of control block TMR FSM can be corrupted *)
Lemma stepg1_tcb  : forall  ccc  ttt, stepg (tmr (ctrBl_dtr false false true)) {~0, ~0, ~0} ttt ccc
                -> (corrupt_1in3_bus1 {~1,~0,~0,~0,~0} ttt /\ corrupt_1in3_cir1 (ctrBl_dtr false false  false) ccc)
                \/ (corrupt_1in3_bus2 {~1,~0,~0,~0,~0} ttt /\ corrupt_1in3_cir2 (ctrBl_dtr false false  false) ccc)
                \/ (corrupt_1in3_bus3 {~1,~0,~0,~0,~0} ttt /\ corrupt_1in3_cir3 (ctrBl_dtr false false  false) ccc).
Proof.
intros ccc ttt. eapply tmr_stepg; Simpl.
assert ( exists t, exists c', step (ctrBl_dtr false false true) (~0) t c' ). apply step_all_ex.
Simpl. assert (HA :=  H). apply fact_stepCtrBl_21 in H. destruct H; Simpl.
Qed.

(*If a glitch happens then either one of tree TMR FSM is corrupted or the control block output is glitched *)
Lemma stepg1_tcbv : forall ttt  ccc, stepg (ctrBlockTMR false false true) {~0,~0,~0} ttt ccc
                        -> (introglitch {~1,~0,~0,~0,~0} ttt /\ ccc= ctrBlockTMR false false false)
                        \/ (exists ctrTMR, ttt= {~1,~0,~0,~0,~0} /\ ccc=ctrTMR -o- ctrVoting
                                           /\ corrupt_1in3_cir (ctrBl_dtr false false false) ctrTMR).
Proof.
introv H. unfold ctrBlockTMR in H. apply inv_stepgS in H. destruct H.
 - repeat destruct H. rename x into c1. rename x0 into c2. rename x1 into t. destruct H0.
   apply stepg1_tcb in H. assert (Hcopy:=H0).
   Rcomb. clear C.
   repeat  destruct H.
    +  right. exists c1. repeat split.
       * Inverts H. eapply  votInpGl1. right. right. exact Hcopy.
       * apply Ccle1_1. apply H1.
    +  Inverts H. right. exists c1. repeat split.
       * eapply  votInpGl1. right. left. exact Hcopy.
       * apply Ccle1_2. apply H1.
    +  Inverts H. right. exists c1. repeat split.
       * eapply  votInpGl1. left. exact Hcopy.
       * apply Ccle1_3. apply H1.
 - repeat destruct H.  rename x into c1. rename x0 into c2. rename x1 into t. destruct H0.
   assert (Hcopy:=H0). Rcomb. left. clear C.
   assert ( step ((ctrBl_dtr false false true)) (~0)  {~1,~0,~0,~0,~0}(ctrBl_dtr false false false)).
   + assert ( exists t, exists c', step (ctrBl_dtr false false true) (~0) t c' ). apply step_all_ex.
     Simpl. assert (HA :=  H1). apply fact_stepCtrBl_21 in H1. destruct H1; Simpl.
   + apply tmr_normal with (s:=~0) in H1.
     apply det_step with (c1:= (tmr (ctrBl_dtr false false false)))
                         (t1:= {~ 1, ~ 0, ~ 0, ~ 0, ~ 0,
                               {~ 1, ~ 0, ~ 0, ~ 0, ~ 0},
                               {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}}) in H.
       * destruct H. symmetry in H. symmetry in H2. Inverts H. Inverts H2.
         clear H3. clear H. split; try easy. unfold ctrBlockTMR. apply stepg1_vot in Hcopy.
         destruct Hcopy. clear H2. destruct H as [H|[H|[H|[H|[H|H]]]]]; Inverts H; easy.
       * Checkpure.
       * apply H1.
Qed.

(*If during an even clock cycle one of redundant fail signals is glitched, the one of three redundant copies
 of control block becomes corrupted *)
Lemma step1_tcbv_i_state  : forall ttt ccc sss, corrupt_1in3_bus (~0) sss
               -> step (ctrBlockTMR false false true) sss ttt  ccc
               -> exists ctrTMR, ccc =(ctrTMR -o- ctrVoting)/\(corrupt_1in3_cir (ctrBl_dtr false false false) ctrTMR).
Proof.
introv H H0. unfold ctrBlockTMR in H0. apply inv_stepS in H0. repeat destruct H0.
rename x into c1. rename x0 into c2. rename x1 into t. destruct H1.
exists c1. Rcomb.  split. easy. Inverts H.
  - eapply tmr_fault3 in H0. destruct H0.
    + apply Ccle1_3. apply H0.
    + Checkpure.
    + Simpl.
    + assert ( exists t, exists c', step (ctrBl_dtr false false true) (~0) t c' ). apply step_all_ex.
      Simpl. assert (HA :=  H). apply fact_stepCtrBl_21 in H. destruct H; Simpl.
 - eapply tmr_fault2 in H0. destruct H0.
    + apply Ccle1_2. apply H0.
    + Checkpure.
    + Simpl.
    + assert ( exists t, exists c', step (ctrBl_dtr false false true) (~0) t c' ). apply step_all_ex.
      Simpl. assert (HA := H). apply fact_stepCtrBl_21 in H. destruct H; Simpl.
 - eapply tmr_fault1 in H0. destruct H0.
    + apply Ccle1_1. apply H0.
    + Checkpure.
    + Simpl.
    + assert ( exists t, exists c', step (ctrBl_dtr false false true) (~0) t c' ). apply step_all_ex.
      Simpl. assert (HA :=  H). apply fact_stepCtrBl_21 in H. destruct H; Simpl.
Qed.

(*If during an even clock cycle one of redundant fail signals is glitched, the output is still correct*)
Lemma step1_tcbv_i_out  : forall  sss ttt ccc, corrupt_1in3_bus (~0) sss
                -> step (ctrBlockTMR false false true) sss ttt ccc
                -> ttt={~1,~0,~0,~0,~0}.
Proof.
introv H H0. unfold ctrBlockTMR in H0. apply inv_stepS in H0.
repeat destruct H0. destruct H1.
assert (HE: step ((ctrBl_dtr false false true)) (~0) {~1,~0,~0,~0,~0} (ctrBl_dtr false false false)).
 - assert ( HEE: exists t, exists c', step (ctrBl_dtr false false true) (~0) t c' ). apply step_all_ex.
   Simpl. assert (HA :=  H2). apply fact_stepCtrBl_21 in H2. destruct H2. Inverts H2.  Inverts H3. exact HA.
 - rename x0 into c2. Inverts H.
   + eapply tmr_fault3 in H0.
     Focus 2. assert (pure_bset (~0)); try easy; exact H. Focus 3. apply HE.
     destruct H0; Inverts H.
     assert (step ctrVoting {~ 1, ~ 0, ~ 0, ~ 0, ~ 0, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}, t0} ttt c2 \/
             step ctrVoting {~ 1, ~ 0, ~ 0, ~ 0, ~ 0, t0, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}} ttt c2 \/
             step ctrVoting { t0, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}} ttt c2
                                                         -> ttt={~1,~0,~0,~0,~0} /\c2=ctrVoting
     ) by apply votInpGl1;  destruct H. left. apply H1. apply H. constructor.
   + eapply tmr_fault2 in H0.
     Focus 2. assert (pure_bset (~0)); try easy; exact H. Focus 3. apply HE.
     destruct H0; Inverts H.
     assert (step ctrVoting {~ 1, ~ 0, ~ 0, ~ 0, ~ 0, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}, t0} ttt c2 \/
             step ctrVoting {~ 1, ~ 0, ~ 0, ~ 0, ~ 0, t0, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}} ttt c2 \/
             step ctrVoting { t0, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}} ttt c2
                                                         -> ttt={~1,~0,~0,~0,~0} /\c2=ctrVoting
     ) by apply votInpGl1. destruct H. right. left. apply H1. apply H. constructor.
   + eapply tmr_fault1 in H0.
     Focus 2. assert (pure_bset (~0)); try easy; exact H. Focus 3. apply HE.
     destruct H0; Inverts H.
     assert (step ctrVoting {~ 1, ~ 0, ~ 0, ~ 0, ~ 0, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}, t0} ttt c2 \/
             step ctrVoting {~ 1, ~ 0, ~ 0, ~ 0, ~ 0, t0, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}} ttt c2 \/
             step ctrVoting { t0, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}} ttt c2
                                                         -> ttt={~1,~0,~0,~0,~0} /\c2=ctrVoting
     ) by apply votInpGl1. destruct H. right. right. apply H1. apply H. constructor.
Qed.


(*If the input bus of zeros is glitched during even cycles, then the output of control block is still correct
  but one of three redundant copies of internal control block FSM can be corrupted*)
Lemma step1_tcbv_i: forall  ttt  sss ccc, corrupt_1in3_bus (~0) sss
              -> step (ctrBlockTMR false false true) sss ttt ccc
              -> ttt={~1,~0,~0,~0,~0} /\ (exists ctrTMR, ccc=(ctrTMR -o- ctrVoting)
                 /\corrupt_1in3_cir (ctrBl_dtr false false false) ctrTMR ).
Proof.
introv H H0. assert (Hc:=H0). Apply  step1_tcbv_i_out   in H0. split.
 -  apply H0.
 -  apply step1_tcbv_i_state  in Hc.
   + destruct Hc. destruct H1. exists x. split. apply H1. apply H2.
   + apply H.
Qed.


(*If during an even clock cycle one of redundant fail signals is glitched, the output is still correct*)
Lemma stepr1_tcbv_i_out: forall  sss ttt ccc, corrupt_1in3_bus (~1) sss
             -> step (ctrBlockTMR false false true) sss ttt ccc
             -> ttt={~1,~1,~1,~1,~1}.
Proof.
introv H H0. unfold ctrBlockTMR in H0. apply inv_stepS in H0.
repeat destruct H0. destruct H1.
assert (HE: step ((ctrBl_dtr false false true)) (~1) {~1,~1,~1,~1,~1} (ctrBl_dtr false true false)).
 - assert ( HEE: exists t, exists c', step (ctrBl_dtr false false true) (~1) t c' ). apply step_all_ex.
   Simpl. assert (HA := H2). apply fact_stepCtrBl_23 in H2. destruct H2. Inverts H2.  Inverts H3. exact HA.
 - rename x0 into c2. Inverts H.
   + eapply tmr_fault3 in H0.
     Focus 2. assert (pure_bset (~1)). easy. exact H. Focus 3. apply HE.
     destruct H0; Inverts H.
     assert (
         step ctrVoting {~1,~1,~1,~1,~1, {~1,~1,~1,~1,~1}, t0} ttt c2 \/
         step ctrVoting {~1,~1,~1,~1,~1, t0, {~1,~1,~1,~1,~1}} ttt c2 \/
         step ctrVoting { t0, {~1,~1,~1,~1,~1}, {~1,~1,~1,~1,~1}} ttt c2 -> ttt={~1,~1,~1,~1,~1} /\c2=ctrVoting
     ) by apply votInpGlRec. destruct H. left. apply H1. apply H. constructor.
   + eapply tmr_fault2 in H0.
     Focus 2. assert (pure_bset (~1)). easy. exact H. Focus 3. apply HE.
     destruct H0; Inverts H.
     assert (
         step ctrVoting {~1,~1,~1,~1,~1, {~1,~1,~1,~1,~1}, t0} ttt c2 \/
         step ctrVoting {~1,~1,~1,~1,~1, t0, {~1,~1,~1,~1,~1}} ttt c2 \/
         step ctrVoting { t0, {~1,~1,~1,~1,~1}, {~1,~1,~1,~1,~1}} ttt c2 -> ttt={~1,~1,~1,~1,~1} /\c2=ctrVoting
     ) by apply votInpGlRec. destruct H. right. left. apply H1. apply H. constructor.
   + eapply tmr_fault1 in H0.
     Focus 2. assert (pure_bset (~1)). easy. exact H. Focus 3. apply HE.
     destruct H0; Inverts H.
     assert (
         step ctrVoting {~1,~1,~1,~1,~1, {~1,~1,~1,~1,~1}, t0} ttt c2 \/
         step ctrVoting {~1,~1,~1,~1,~1, t0, {~1,~1,~1,~1,~1}} ttt c2 \/
         step ctrVoting { t0, {~1,~1,~1,~1,~1}, {~1,~1,~1,~1,~1}} ttt c2 -> ttt={~1,~1,~1,~1,~1} /\c2=ctrVoting
     ) by apply votInpGlRec. destruct H. right. right. apply H1. apply H. constructor.
Qed.

(*If during an even clock cycle one of redundant fail signals is glitched, the one of three redundant copies
 of control block becomes corrupted *)
Lemma stepr1_tcbv_i_state  : forall ttt ccc sss, corrupt_1in3_bus (~1) sss
               -> step (ctrBlockTMR false false true) sss ttt  ccc
               -> exists ctrTMR, ccc =(ctrTMR -o- ctrVoting)/\
                               (corrupt_1in3_cir (ctrBl_dtr  false true false) ctrTMR ).
Proof.
introv H H0. unfold ctrBlockTMR in H0. apply inv_stepS in H0. repeat destruct H0.
rename x into c1. rename x0 into c2. rename x1 into t. destruct H1.
exists c1. Rcomb. split. easy. Inverts H.
  - eapply tmr_fault3 in H0. destruct H0.
     + apply Ccle1_3. apply H0.
     + assert (pure_bset (~1)). easy. exact H.
     + constructor.
     + assert ( exists t, exists c', step (ctrBl_dtr false false true) (~1) t c' ). apply step_all_ex.
       Simpl. assert (HA := H). apply fact_stepCtrBl_23 in H. destruct H; Simpl.
  - eapply tmr_fault2 in H0. destruct H0.
     + apply Ccle1_2. apply H0.
     + assert (pure_bset (~1)). easy. exact H.
     + constructor.
     + assert ( exists t, exists c', step (ctrBl_dtr false false true) (~1) t c' ). apply step_all_ex.
       Simpl. assert (HA := H). apply fact_stepCtrBl_23 in H. destruct H; Simpl.
  - eapply tmr_fault1 in H0. destruct H0.
     + apply Ccle1_1. apply H0.
     + assert (pure_bset (~1)). easy. exact H.
     + constructor.
     + assert (exists t, exists c', step (ctrBl_dtr false false true) (~1) t c' ). apply step_all_ex.
       Simpl. assert (HA := H). apply fact_stepCtrBl_23 in H. destruct H; Simpl.
Qed.

(*If the input bus of ones is glitched during even cycles, then the output of control block is still correct
  but one of three redundant copies of internal control block FSM can be corrupted*)
Lemma stepr1_tcbv_i: forall  ttt  sss ccc, corrupt_1in3_bus (~1) sss
                   -> step (ctrBlockTMR false false true) sss ttt ccc
                   -> ttt={~1,~1,~1,~1,~1} /\ (exists ctrTMR, ccc=(ctrTMR -o- ctrVoting)/\
                              corrupt_1in3_cir (ctrBl_dtr false true false) ctrTMR ).
Proof.
introv H H0. assert (Hc:=H0). apply stepr1_tcbv_i_out in H0. split.
 -  apply H0.
 -  apply stepr1_tcbv_i_state in Hc.
   + destruct Hc. destruct H1. exists x. split. apply H1. apply H2.
   + apply H.
 - apply H.
Qed.