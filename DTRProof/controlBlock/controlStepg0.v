(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-  ctr block properties during odd(0) cycles with a glitch

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
(** Properties of DTR control block during an odd(0) cycles  with a GLITCH *)
(* ####################################################################### *)

(*If a glitch happens then only one redudant copy of control block TMR FSM can be corrupted *)
Lemma stepg0_tcb  : forall  ccc fI ttt, pure_bset fI -> stepg (tmr (ctrBl_dtr false false false)) {fI,fI,fI} ttt ccc
                -> (corrupt_1in3_bus1 {~0,~0,~0,~0,~0} ttt /\ corrupt_1in3_cir1 (ctrBl_dtr false false true) ccc)
                \/ (corrupt_1in3_bus2 {~0,~0,~0,~0,~0} ttt /\ corrupt_1in3_cir2 (ctrBl_dtr false false true) ccc)
                \/ (corrupt_1in3_bus3 {~0,~0,~0,~0,~0} ttt /\ corrupt_1in3_cir3 (ctrBl_dtr false false true) ccc).
Proof.
intros ccc fI ttt P. eapply tmr_stepg; Simpl. 
assert ( exists t, exists c', step (ctrBl_dtr false false false) fI t c' ). apply step_all_ex.
Simpl. assert (HA :=  H). apply fact_stepCtrBl_12 in H. destruct H; Simpl.
Qed.

(*If a glitch happens then either one of tree TMR FSM is corrupted or the control block output is glitched *)
Lemma stepg0_tcbv : forall fI ttt ccc, pure_bset fI -> stepg (ctrBlockTMR false false false) {fI,fI,fI} ttt ccc
                        -> (introglitch {~0,~0,~0,~0,~0} ttt /\ ccc= ctrBlockTMR false false true)
                            \/ (exists ctrTMR, ttt= {~0,~0,~0,~0,~0} /\ ccc=ctrTMR -o- ctrVoting
                                           /\ corrupt_1in3_cir (ctrBl_dtr false false true) ctrTMR).
Proof. 
introv P H. unfold ctrBlockTMR in H. apply inv_stepgS in H. destruct H.
 - repeat destruct H. rename x into c1. rename x0 into c2. rename x1 into t. destruct H0.
   apply stepg0_tcb in H. assert (Hcopy:=H0). Rcomb. clear C. 
   repeat destruct H.
    +  right. exists c1. repeat split.
       * Inverts H. eapply  votInpGl0. right. right. exact Hcopy.
       * apply Ccle1_1. apply H1.
    +  Inverts H. right. exists c1. repeat split.
       * eapply  votInpGl0. right. left. exact Hcopy.
       * apply Ccle1_2. apply H1.
    +  Inverts H. right. exists c1. repeat split.
       * eapply  votInpGl0. left. exact Hcopy.
       * apply Ccle1_3. apply H1.
    + Checkpure. 
 - repeat destruct H.  rename x into c1. rename x0 into c2. rename x1 into t. destruct H0.
   assert (Hcopy:=H0). Rcomb. left. clear C.
   assert (forall fS, step ((ctrBl_dtr false false false)) fS  {~0,~0,~0,~0,~0}(ctrBl_dtr false false true)).
   + intro. assert ( exists t, exists c', step (ctrBl_dtr false false false) fS t c' ). apply step_all_ex.
     Simpl. assert (HA := H1). apply fact_stepCtrBl_12 in H1. destruct H1; Simpl.
   + apply tmr_normal with (s:=fI) in H1. Rdet. apply stepg0_vot in Hcopy.
     split; try easy. destruct Hcopy. destruct H1 as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]]; Inverts Hx; easy.
Qed.

(*If during an even clock cycle one of redundant fail signals is glitched, the output is still correct*)
Lemma step0_tcbv_i_out: forall fI sss ttt ccc, pure_bset fI -> corrupt_1in3_bus fI sss
                -> step (ctrBlockTMR false false false) sss ttt ccc
                -> ttt={~0,~0,~0,~0,~0}.
Proof.
introv P H H0. unfold ctrBlockTMR in H0. apply inv_stepS in H0.
repeat destruct H0. destruct H1.
assert (HE: step ((ctrBl_dtr false false false)) fI {~0,~0,~0,~0,~0} (ctrBl_dtr false false true)).
 - assert ( HEE: exists t, exists c', step (ctrBl_dtr false false false) fI t c' ). apply step_all_ex.
   Simpl. assert (HA := H2). apply fact_stepCtrBl_12 in H2. destruct H2. Inverts H2.  Inverts H3. exact HA.
 - rename x0 into c2. Inverts H.
   + eapply tmr_fault3 in H0.
     Focus 2. apply P. Focus 3. apply HE.
     destruct H0; Inverts H. 
     assert ( step ctrVoting {~ 0, ~ 0, ~ 0, ~ 0, ~ 0, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}, t0} ttt c2 \/
              step ctrVoting {~ 0, ~ 0, ~ 0, ~ 0, ~ 0, t0, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}} ttt c2 \/
              step ctrVoting { t0, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}} ttt c2 
                                                          -> ttt={~0,~0,~0,~0,~0} /\c2=ctrVoting
     ) by apply votInpGl0;  destruct H. left. apply H1. apply H. constructor. 
   + eapply tmr_fault2 in H0.
     Focus 2. apply P. Focus 3. apply HE.
     destruct H0; Inverts H. 
     assert ( step ctrVoting {~ 0, ~ 0, ~ 0, ~ 0, ~ 0, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}, t0} ttt c2 \/
              step ctrVoting {~ 0, ~ 0, ~ 0, ~ 0, ~ 0, t0, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}} ttt c2 \/
              step ctrVoting { t0, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}} ttt c2 
                                                          -> ttt={~0,~0,~0,~0,~0} /\c2=ctrVoting
     ) by apply votInpGl0;  destruct H. right. left. apply H1. apply H. constructor. 
   + eapply tmr_fault1 in H0.
     Focus 2. apply P. Focus 3. apply HE.
     destruct H0; Inverts H. 
     assert ( step ctrVoting {~ 0, ~ 0, ~ 0, ~ 0, ~ 0, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}, t0} ttt c2 \/
              step ctrVoting {~ 0, ~ 0, ~ 0, ~ 0, ~ 0, t0, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}} ttt c2 \/
              step ctrVoting { t0, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}} ttt c2 
                                                          -> ttt={~0,~0,~0,~0,~0} /\c2=ctrVoting
     ) by apply votInpGl0;  destruct H. right. right. apply H1. apply H. constructor. 
Qed.

(*If during an odd clock cycle one of redundant fail signals is glitched, the one of three redundant copies 
 of control block becomes corrupted *)
Lemma step0_tcbv_i_state  : forall   fI ttt ccc sss, 
                   pure_bset fI -> corrupt_1in3_bus fI sss
                -> step (ctrBlockTMR false false false) sss ttt ccc
                -> exists ctrTMR, ccc =(ctrTMR -o- ctrVoting)/\ 
                               (corrupt_1in3_cir (ctrBl_dtr false false true) ctrTMR ).
Proof.
introv P H H0. unfold ctrBlockTMR in H0. apply inv_stepS in H0. repeat destruct H0.
rename x into c1. rename x0 into c2. rename x1 into t. destruct H1.
exists c1. Rcomb.  split. easy. Inverts H.
  - eapply tmr_fault3 in H0. destruct H0.
    + apply Ccle1_3. apply H0. 
    + apply P.
    + constructor.
    + assert ( exists t, exists c', step (ctrBl_dtr false false false) fI t c' ). apply step_all_ex.
      Simpl. assert (HA :=  H). apply fact_stepCtrBl_12 in H. destruct H; Simpl.
 - eapply tmr_fault2 in H0. destruct H0.
    + apply Ccle1_2. apply H0. 
    + apply P. 
    + constructor. 
    + assert ( exists t, exists c', step (ctrBl_dtr false false false) fI t c' ). apply step_all_ex.
      Simpl. assert (HA := H). apply fact_stepCtrBl_12 in H. destruct H; Simpl.
 - eapply tmr_fault1 in H0. destruct H0.
    + apply Ccle1_1. apply H0. 
    + apply P. 
    + constructor. 
    + assert ( exists t, exists c', step (ctrBl_dtr false false false) fI t c' ). apply step_all_ex.
      Simpl. assert (HA :=  H). apply fact_stepCtrBl_12 in H. destruct H; Simpl.
Qed.

(*If the input bus is glitched during odd cycles, then the output of control block is still correct
  but one of three redundant copies of internal control block FSM can be corrupted*)
Lemma step0_tcbv_i: forall fI ttt sss ccc, pure_bset fI -> corrupt_1in3_bus fI sss
                  -> step (ctrBlockTMR false false false) sss ttt ccc
                  -> ttt={~0,~0,~0,~0,~0} /\ (exists ctrTMR, ccc=(ctrTMR -o- ctrVoting)
                              /\corrupt_1in3_cir (ctrBl_dtr false false true) ctrTMR ).
Proof.
introv P H H0. assert (Hc:=H0). apply  step0_tcbv_i_out with (fI:=fI) in H0. split.
 -  apply H0.
 -  apply step0_tcbv_i_state with (fI:=fI) in Hc. 
   + destruct Hc. destruct H1. exists x. split. apply H1. apply H2.
   + apply P.
   + apply H.
 - apply P.
 - apply H.
Qed.