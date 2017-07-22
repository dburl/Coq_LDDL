(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation
#</h1>#
- states transitions with a glitch for memoty block
  during odd(0) cycles

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)


Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import dtrTransform relationPred relationProp leftStep leftStepg.
Require Import rightStep memoryInv0 memoryStep rightStepg.

Set Implicit Arguments.

(* ##################################################################### *)
(** Properties of Memory Block with a Glitches during odd(0) cycles      *)
(* ##################################################################### *)

Lemma step0_mb_f : forall S T (c c' c'':circuit S T) c2 c2' t2 s t  f,
                        pure_bset s -> dtrs0 c c' c2
                     -> step c' s t c''
                     -> step c2 {s,{~0,~0,f}} t2 c2'
                     -> (t2 = {t,{~0,~0,f}}) /\ dtrs1 c c' c'' c2'.
Proof.
intros S T c. induction c; introv P1 R H HT; Inverts R; unfold dtrs1.
- Invstep HT. Inverts H1. split; Simpl.
- Invstep HT. Inverts H1. split; Simpl.
- Inverts H. Inverts HT. SimpS.
  Apply IHc1 with H4 H5 in H3. Simpl.
  Apply IHc2 with H11 in H12. Simpl.
- unfold  SWAP_LR in HT. unfold  SWAP_LS in HT.
  Invstep HT. SimpS.
  Apply IHc1 with H2 H0 in H3. SimpS.
  Apply IHc2 with H10 H11 in H9. SimpS.
  split; try constructor; easy.
- Inverts H7.
  unfold memBlock in HT. unfold lhsMB in HT. unfold rhsMB in HT.
  Invstep HT. SimpS.
  apply step_rhs in H15. SimpS.
  Destruct_s f; destruct x.
  + apply step_lhs with (sav:=false) (rol:=false)
                        (d:=r) (r:=r) (fai:=false) in H18; try easy.
    SimpS; cbn in H2; rewrite eqb_reflx in H2;
    Apply IHc with H4 H6 in H2;
    cbn in H1; rewrite s2bob2s in H1; Inverts H1; SimpS;
    split; Simpl; repeat constructor; easy.
  + apply step_lhs with (sav:=false) (rol:=false)
                        (d:=r) (r:=r) (fai:=true) in H18; try easy.
    SimpS; cbn in H2; rewrite eqb_reflx in H2;
    Apply IHc with H4 H6 in H2;
    cbn in H1; rewrite s2bob2s in H1; Inverts H1; SimpS;
    split; Simpl; repeat constructor; easy.
  + apply step_lhs_f with (sav:=false) (rol:=false)
                          (d:=r) (r:=r) in H18; try easy.
    SimpS; cbn in H2; rewrite eqb_reflx in H2;
    Apply IHc with H4 H6 in H2;
    cbn in H1; rewrite s2bob2s in H1; Inverts H1; SimpS;
    split; Simpl; repeat constructor; easy.
Qed.

(*If the control input save signal is glitched, then save output is also glitched
  and internal state is corrupted *)
 Lemma step0_mb_s : forall S T (c c' c'':circuit S T) c2 c2' t2 s t,
                        pure_bset s -> dtrs0 c c' c2
                     -> step c' s t c''
                     -> step c2 {s,{~?,~0,~0}} t2 c2'
                     -> t2 = {t,{~?,~0,~0}} /\ dtr1_rr' c c' c'' c2'.
Proof.
introv P R H HT. induction H.
- Inverts R. Invstep HT. Simpl; repeat constructor.
- Inverts R. Invstep HT; Simpl; repeat constructor.
- destruct c; Inverts R. Inverts HT.
  Apply IHstep1 in H6;  Simpl.
  Apply IHstep2 in H12; Simpl.
  repeat constructor; easy.
- Inverts R. unfold SWAP_LS in HT. unfold SWAP_LR in HT.
  Invstep HT. SimpS.
  Apply IHstep1 in H0; Simpl.
  Apply IHstep2 in H11; Simpl.
  repeat constructor; easy.
- Inverts R. Inverts H8. unfold memBlock in HT.
  unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS.
  apply step_rhs in H16.
  apply step_lhs_s with (fai:=false) (rol:=false) (d:= r) (r:= r)  in H19; try easy.
  SimpS. cbn in H2. rewrite eqb_reflx in H2. unfold bool2bset in H2. cbn in H2.
  Apply IHstep with H7 in H2. Simpl.
  destruct H3; Inverts H; Simpl; repeat constructor; easy.
Qed.

(*If the control input rollback signal is glitched, then d cell is corrupted as
 well as rollback output*)
Lemma step0_mb_b : forall S T (c c' c'':circuit S T) c2 c2' t2 s t  x,
                         dtrs0 c c' c2
                     -> step c' s t c''
                     -> step c2 {x,{~0,~?,~0}} t2 c2'
                     -> exists x', t2 = {x',{~0,~?,~0}} /\ dtr1_d c c' c'' c2'.
Proof.
introv R H HT. induction H.
- Inverts R; Invstep HT; Simpl. exists (redgate g x); split; constructor.
- Inverts R; Invstep HT; Simpl. exists (redplug p x); split; constructor.
- destruct c; Inverts R. Inverts HT.
  Apply IHstep1 in H6;  Simpl.
  Apply IHstep2 in H12; Simpl. exists x. split; constructor; easy.
- Inverts R. unfold SWAP_LS in HT. unfold SWAP_LR in HT.
  Invstep HT. SimpS.
  Apply IHstep1 in H0; Simpl.
  Apply IHstep2 in H11; Simpl.
  exists {x1,x}. split; Simpl. constructor; easy.
- Inverts R. Inverts H8. unfold memBlock in HT.
  unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS.
  apply step_rhs in H16.
  apply step_lhs_b with (fai:=false) (sav:=false) (d:= r) (r:= r)  in H19; try easy.
  SimpS. simpl in H2. rewrite eqb_reflx in H2. simpl in H2. unfold bool2bset in H2. simpl in H2.
  apply IHstep with (c:=c1) in H2; Simpl. simpl in H1. rewrite s2bob2s in H1. Inverts H1.
  exists x1. split; constructor; Simpl. simpl. constructor.
Qed.

(*If the data input f signal is glitched, then d cell is corrupted as
 well as data output; control wires are {~0,~0,~0}*)
Lemma step0_mb_i : forall S T (c c' c'':circuit S T) c2 c2' t2 s t f,
                      dtrs0 c c' c2
                   -> step c' s t c''
                   -> step c2 {f,{~0,~0,~0}} t2 c2'
                   ->  (exists e, t2 = {e,{~0,~0,~0}}) /\ dtr1_d c c' c'' c2'.
Proof.
introv R H HT. induction H.
- Inverts R; split; Invstep HT; Simpl. constructor.
- Inverts R; split; Invstep HT; Simpl. constructor.
- destruct c; Inverts R. Inverts HT.
  Apply IHstep1 in H6;  Simpl.
  Apply IHstep2 in H12; Simpl. split; Simpl. constructor; easy.
- Inverts R. unfold SWAP_LS in HT. unfold SWAP_LR in HT.
  Invstep HT. SimpS.
  Apply IHstep1 in H0; Simpl.
  Apply IHstep2 in H11; Simpl.
  split; Simpl. constructor; easy.
- Inverts R. Inverts H8. unfold memBlock in HT.
  unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS.
  apply step_rhs in H16.
  apply step_lhs  with (d:=r) (r:=r)(sav:=false) (rol:=false) (fai:=false) in H19; try easy.
  SimpS. simpl in H2. rewrite eqb_reflx in H2. simpl in H2. unfold bool2bset in H2. simpl in H2.
  apply IHstep with (c:=c1) in H2; Simpl. simpl in H1. rewrite s2bob2s in H1. Inverts H1.
  split; Simpl; constructor; try easy. constructor.
Qed.

(*If the data input f1 signal is glitched, then d cell is corrupted as
 well as data output; control wires are {~0,~0, known prossibly glitched} propagates
 through a memory block*)
Lemma step0_mb_if : forall S T (c c' c'':circuit S T) c2 c2' t2 s t f1 f2,
                      dtrs0 c c' c2
                   -> step c' s t c''
                   -> step c2 {f1,{~0,~0,f2}} t2 c2'
                   -> (exists e1 e2, t2 = {e1,{~0,~0,e2}}) /\ dtr1_d c c' c'' c2'.
Proof.
intros S T c. induction c.
- introv R H HT. Inverts R. Invstep HT. Inverts H1. split; Simpl. constructor.
- introv R H HT. Inverts R. Invstep HT. Inverts H1. split; Simpl. constructor.
- introv R H HT. Inverts R. Inverts H. Inverts HT. Simpl.
  apply IHc1 with (c':=c1') (c'':= c1'0) (t:=t0) (s:=s) in H3; Simpl.
  apply IHc2 with (c':=c2'0) (c'':=c2'1) (t:=t) (s:=t0) in H12; Simpl.
  split; Simpl. constructor; easy.
- introv R H HT. Inverts R. unfold  SWAP_LR in HT. unfold  SWAP_LS in HT.
  Invstep HT. SimpS.
  apply IHc1 with (c'':=x25) (c2':=x18) (t2:={x7, {x11, x12, x10}}) (s:=x3) (t:=x1) (f1:=x)(f2:=f2) in H3; Simpl.
  apply IHc2 with (c'':=x33) (c2':=x35) (t2:={x13, {x16, x17, x15}}) (s:=x4) (t:=x2) (f1:=x0)(f2:=x6) in H9; Simpl.
  split; Simpl. constructor; easy.
- introv R H HT. Inverts R. Inverts H7. unfold memBlock in HT. unfold lhsMB in HT.
  unfold rhsMB in HT. Invstep HT. SimpS.
  apply step_rhs in H15. SimpS.
  Destruct_s f2; destruct x.
   + apply step_lhs with  (sav:=false) (rol:=false) (d:= r) (r:= r) (fai:=false) in H18; try easy.
     SimpS. unfold bool2bset in H2. simpl in H2. rewrite eqb_reflx in H2.
     simpl in H2. simpl in H1. rewrite s2bob2s in H1. Inverts H1.
     apply IHc with (c':=c'0) (c'':=x3) (t:={t, x71}) (s:={s, bool2bset x68}) in H2; try easy; Checkpure;
     destruct H2; Simpl.
   + apply step_lhs with  (sav:=false) (rol:=false) (d:= r) (r:= r) (fai:=true) in H18; try easy.
     SimpS. unfold bool2bset in H2. simpl in H2. rewrite eqb_reflx in H2.
     simpl in H2. simpl in H1. rewrite s2bob2s in H1. Inverts H1.
     apply IHc with (c':=c'0) (c'':=x3) (t:={t, x71}) (s:={s, bool2bset x68}) in H2; try easy; Checkpure;
     destruct H2; Simpl.
   + apply step_lhs_f with  (sav:=false) (rol:=false) (d:= r) (r:= r)  in H18; try easy.
     SimpS. unfold bool2bset in H2. simpl in H2. rewrite eqb_reflx in H2.
     simpl in H2. simpl in H1. rewrite s2bob2s in H1. Inverts H1.
     apply IHc with (c':=c'0) (c'':=x3) (t:={t, x71}) (s:={s, bool2bset x68}) in H2; try easy; Checkpure;
     destruct H2; Simpl.
Qed.

(*-------------------------- IF CURRENT STATE IS CORRUPTED -------------------------*)


(*If the data input f signal is glitched, then d cell is corrupted as
 well as data output; control wires are {~0,~0,~1}*)
Lemma step0_mb_id' : forall S T (c c' c'':circuit S T) c2 c2' t2 s t e,
                      dtr0_d' c c' c2
                   -> step c' s t c''
                   -> step c2 {e,{~0,~0,~1}} t2 c2'
                   -> (exists e1, t2 = {e1,{~0,~0,~1}}) /\ dtr1_d c c' c'' c2'.
Proof.
introv R H HT. induction H.
- Inverts R; split; Invstep HT; Simpl. constructor.
- Inverts R; split; Invstep HT; Simpl. constructor.
- destruct c; Inverts R. Inverts HT.
  Apply IHstep1 in H6;  Simpl.
  Apply IHstep2 in H12; Simpl. split; Simpl. constructor; easy.
- Inverts R. unfold SWAP_LS in HT. unfold SWAP_LR in HT.
  Invstep HT. SimpS.
  Apply IHstep1 in H0; Simpl.
  Apply IHstep2 in H11; Simpl.
  split; Simpl. constructor; easy.
- Inverts R. unfold memBlock in HT.
  unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS. Inverts H8.
  apply step_rhs in H17.
  apply step_lhs  with (d:=r) (r:=r)(sav:=false) (rol:=false) (fai:=true) in H20; try easy.
  SimpS. simpl in H1. rewrite s2bob2s in H1. Inverts H1. simpl in H2.
  assert (HX:(negb (eqb d' x68) || true)=true) by (destruct (negb (eqb d' x68)); easy). (*[B]*)
  rewrite HX in H2. unfold bool2bset in H2. simpl in H2.
  apply IHstep with (c:=c1) in H2; Simpl.
  split; Simpl; constructor; try easy. constructor.
Qed.

(**if both d and r memory cells are corruted and control signals are (save, rollback, fail)={~0,~0,~1}*)
(*odd clock cycle*)
Lemma step0_mb_dr  : forall S T (c c' c'':circuit S T) c2 c2' t2 s t,
                       pure_bset s -> dtr0_dr c c' c2
                    -> step c' s t c''
                    -> step c2 {s,{~0,~0,~1}} t2 c2'
                    -> t2 = {t,{~0,~0,~1}} /\ (dtr1_d'r c c' c'' c2').
Proof.
introv P R H HT. induction H.
- Inverts R; split; Invstep HT; Simpl. constructor.
- Inverts R; split; Invstep HT; Simpl. constructor.
- destruct c; Inverts R. Inverts HT.
  Apply IHstep1 in H6;  Simpl.
  Apply IHstep2 in H12; Simpl. split; Simpl. constructor; easy.
- Inverts R. unfold SWAP_LS in HT. unfold SWAP_LR in HT.
  Invstep HT. SimpS.
  Apply IHstep1 in H0; Simpl.
  Apply IHstep2 in H11; Simpl.
  split; Simpl. constructor; easy.
- Inverts R. unfold memBlock in HT.
  unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS. Inverts H8.
  apply step_rhs in H17.
  apply step_lhs  with (d:=d) (r:=r)(sav:=false) (rol:=false) (fai:=true) in H20; try easy.
  SimpS. simpl in H1. rewrite s2bob2s in H1. Inverts H1. simpl in H2.
  assert (HX:(negb (eqb d' d) || true)=true) by (destruct (negb (eqb d' d)); easy). (*[B]*)
  rewrite HX in H2. unfold bool2bset in H2. simpl in H2.
  Apply IHstep in H2; Simpl.
  split; Simpl; constructor; try easy. constructor.
Qed.

(**if both d and r memory cells are corruted and control signals are (save, rollback, fail)={~0,~0,~0}*)
(*odd clock cycle*)
Lemma step0_mb_dr_F  : forall S T (c c' c'':circuit S T) c2 c2' t2 s t,
                       pure_bset s -> dtr0_dr c c' c2
                    -> step c' s t c''
                    -> step c2 {s,{~0,~0,~0}} t2 c2'
                    -> (t2 = {t,{~0,~0,~1}} /\ dtr1_d'r c c' c'' c2')
                    \/ (t2 = {t,{~0,~0,~0}} /\ dtr1_r c c' c'' c2').
Proof.
introv P R H HT. induction H.
- Inverts R. Inverts H. Invstep HT. Simpl.
  right. split; Simpl. constructor.
- Inverts R. Inverts H. Invstep HT. Simpl.
  right. split; Simpl. constructor.
- destruct c; Inverts R. Inverts HT.  SimpS.
  apply IHstep1 with (c:=c3) in H6; try easy. SimpS. destruct H6.
  + SimpS. apply  step0_mb_dr with (c:=c4) (c':=c0) (c'':=c2'0) (t:=u) in H12 ; try easy.
    SimpS. left. split. easy. constructor; Simpl. Simpl.
  + SimpS. apply  IHstep2 with (c:=c4) in H12 ; try easy. destruct H12. left.
    SimpS. split. easy. constructor;  Simpl. apply  dtr1_r_imp_d'r in H2. easy.
    SimpS. right. split. easy. constructor; Simpl. Simpl.
- Inverts R. unfold SWAP_LS in HT. unfold SWAP_LR in HT. Invstep HT. SimpS.
  apply IHstep1 with (c:=c3) in H0; try easy. destruct H0; SimpS.
  + apply  step0_mb_dr with (c:=c4) (c':=c0) (c'':=c2'0) (t:=v) in H11 ; try easy. SimpS.
    left. split. easy. constructor; Simpl.
  + apply IHstep2  with (c:=c4)  in H11; try easy. destruct H11; SimpS.
     * left. split. easy. constructor; Simpl. apply  dtr1_r_imp_d'r in H5. easy.
     * right. split. easy. constructor; Simpl.
- Inverts R. Inverts H8. unfold memBlock in HT. unfold lhsMB in HT. unfold rhsMB in HT.
  Invstep HT. SimpS. apply step_rhs in H16.
  apply step_lhs  with (fai:=false) (sav:=false) (rol:=false) (d:= d) (r:= r)  in H19; try easy.
  simpl in H19. SimpS. simpl in H1. rewrite s2bob2s in H1. Inverts H1.
  destruct d'; destruct d; unfold bool2bset in H2; simpl in H2.
 + Apply IHstep in H2. destruct H2; SimpS.
   * left. split. easy. constructor; Simpl. constructor.
   * right. split. easy. constructor; Simpl. constructor.
   * Simpl.
 + apply step0_mb_dr with (c:=c1) (c':=c0) (c'':=c') (t:={t, a}) in H2; Simpl.
   left. split. easy. constructor; Simpl. constructor.
 + apply step0_mb_dr with (c:=(c1)) (c':=c0) (c'':=c') (t:={t, a}) in H2; Simpl.
   left. split. easy. constructor; Simpl. constructor.
 + Apply IHstep in H2; Simpl. destruct H2; SimpS.
   * left. split. easy. constructor; Simpl. constructor.
   * right. split. easy. constructor; Simpl. constructor.
Qed.

(**If both check-pointing r and r' memory cells are corruted
      and control signals are (save, rollback, fail)={~0,~0,~0},
   the checkpointing mechanisme stays to be corrupted*)
(*odd clock cycle*)
Lemma step0_mb_rr' : forall S T (c c' c'':circuit S T) c2 c2' t2 s t,
                       pure_bset s -> dtr0_rr' c c' c2
                    -> step c' s t c''
                    -> step c2 {s,{~0,~0,~0}} t2 c2'
                    -> t2 = {t,{~0,~0,~0}} /\ dtr1_rr' c c' c'' c2'.
Proof.
 introv P R H HT. induction H.
- Inverts R; split; Invstep HT; Simpl. constructor.
- Inverts R; split; Invstep HT; Simpl. constructor.
- destruct c; Inverts R. Inverts HT.
  Apply IHstep1 in H6;  Simpl.
  Apply IHstep2 in H12; Simpl. split; Simpl. constructor; easy.
- Inverts R. unfold SWAP_LS in HT. unfold SWAP_LR in HT.
  Invstep HT. SimpS.
  Apply IHstep1 in H0; Simpl.
  Apply IHstep2 in H11; Simpl.
  split; Simpl. constructor; easy.
- Inverts R. unfold memBlock in HT.
  unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS. Inverts H8.
  apply step_rhs in H17.
  apply step_lhs  with (d:=d') (r:=r)(sav:=false) (rol:=false) (fai:=false) in H20; try easy.
  SimpS. simpl in H1. rewrite s2bob2s in H1. Inverts H1. simpl in H2.
  rewrite eqb_reflx in H2. simpl in H2. unfold bool2bset in H2. simpl in H2.
  Apply IHstep in H2; Simpl.
  split; Simpl; constructor; try easy. constructor.
Qed.

(**If a check-pointing r' memory cells is corruted
      and control signals are (save, rollback, fail)={~0,~0,~0},
   it stays to be corrupted*)
Lemma step0_mb_r' : forall S T (c c' c'':circuit S T) c2 c2' t2 s t,
                      pure_bset s -> dtr0_r' c c' c2
                   -> step c' s t c''
                   -> step c2 {s,{~0,~0,~0}} t2 c2'
                   -> t2 = {t,{~0,~0,~0}} /\ dtr1_r' c c' c'' c2'.
Proof.
introv P R H HT. induction H.
- Inverts R; split; Invstep HT; Simpl. constructor.
- Inverts R; split; Invstep HT; Simpl. constructor.
- destruct c; Inverts R. Inverts HT.
  Apply IHstep1 in H6;  Simpl.
  Apply IHstep2 in H12; Simpl. split; Simpl. constructor; easy.
- Inverts R. unfold SWAP_LS in HT. unfold SWAP_LR in HT.
  Invstep HT. SimpS.
  Apply IHstep1 in H0; Simpl.
  Apply IHstep2 in H11; Simpl.
  split; Simpl. constructor; easy.
- Inverts R. unfold memBlock in HT.
  unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS. Inverts H8.
  apply step_rhs in H17.
  apply step_lhs  with (d:=r) (r:=r)(sav:=false) (rol:=false) (fai:=false) in H20; try easy.
  SimpS. simpl in H1. rewrite s2bob2s in H1. Inverts H1. simpl in H2.
  rewrite eqb_reflx in H2. simpl in H2. unfold bool2bset in H2. simpl in H2.
  Apply IHstep in H2; Simpl.
  split; Simpl; constructor; try easy. constructor.
Qed.

(**If a check-pointing r' memory cells is corruted
      and control signals are (save, rollback, fail)={~0,~0,~0},
   it stays to be corrupted*)
Lemma step0_mb_r  : forall S T (c c' c'':circuit S T) c2 c2' t2 s t,
                       pure_bset s -> dtr0_r c c' c2
                    -> step c' s t c''
                    -> step c2 {s,{~0,~0,~0}} t2 c2'
                    -> t2 = {t,{~0,~0,~0}} /\ dtr1_r c c' c'' c2'.
Proof.
introv P R H HT. induction H.
- Inverts R; split; Invstep HT; Simpl. constructor.
- Inverts R; split; Invstep HT; Simpl. constructor.
- destruct c; Inverts R. Inverts HT.
  Apply IHstep1 in H6;  Simpl.
  Apply IHstep2 in H12; Simpl. split; Simpl. constructor; easy.
- Inverts R. unfold SWAP_LS in HT. unfold SWAP_LR in HT.
  Invstep HT. SimpS.
  Apply IHstep1 in H0; Simpl.
  Apply IHstep2 in H11; Simpl.
  split; Simpl. constructor; easy.
- Inverts R. unfold memBlock in HT.
  unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS. Inverts H8.
  apply step_rhs in H17.
  apply step_lhs  with (d:=d') (r:=r)(sav:=false) (rol:=false) (fai:=false) in H20; try easy.
  SimpS. simpl in H1. rewrite s2bob2s in H1. Inverts H1. simpl in H2.
  rewrite eqb_reflx in H2. simpl in H2. unfold bool2bset in H2. simpl in H2.
  Apply IHstep in H2; Simpl.
  split; Simpl; constructor; try easy. constructor.
Qed.

(**If d' memory cells is possibly corruted during an odd cycle
    then either it is corrupted and fail signal is raised
         or it is correct and fail signal stays to be zero*)
Lemma step0_mb_d'  : forall S T (c c' c'':circuit S T) c2 c2' t2 s t f,
                       pure_bset s -> pure_bset f -> dtr0_d' c c' c2
                    -> step c' s t c''
                    -> step c2 {s,{~0,~0,f}} t2 c2'
                    -> (t2 = {t,{~0,~0,f}} /\ dtrs1 c c' c'' c2')
                    \/ (exists t', pure_bset t'
                                  /\ t2 = {t',{~0,~0,~1}}
                                  /\ dtr1_d  c c' c'' c2').
Proof.
intros S T c. induction c; unfold dtrs1.
- introv P1 P2 R H HT. Inverts R. Invstep HT. Inverts H. left.
  split; SimpS.  Inverts H1. easy. Simpl.
- introv P1 P2 R H HT. Inverts R. Invstep HT. Inverts H. left.
  split; SimpS. Inverts H1. easy. Simpl.
- introv P1 P2 R H HT. Inverts R. Inverts H. Inverts HT. SimpS.
  apply IHc1 with (c':=c1') (c'':= c1'0) (t:=t0)  in H3;  try easy.
  destruct H3; SimpS. Rpure.
  + apply IHc2 with (c':=c2'0) (c'':=c2'1) (t:=t) in H12 ; try easy.
    destruct H12; SimpS.
    * left. easy.
    * right. exists x. split; try easy. split; try easy. constructor; Simpl.
      apply dtrs1_imp_dtr1_d in H0. easy.
  + Simpl. apply step0_mb_id' with (c:=c2) (c':=c2'0) (c'':=c2'1) (s:=t0) (t:=t)  in H12; try easy.
    * Simpl. right. exists x. repeat split; Simpl. repeat constructor; Simpl.
- introv P1 P2 R H HT. Inverts R. unfold  SWAP_LR in HT. unfold  SWAP_LS in HT.
  Invstep HT. SimpS.
  apply IHc1 with (c'':=x25) (c2':=x18) (t2:={x5, {x11, x12, x10}})
                  (s:=x1) (t:=x) (f:=f)  in H3;  try easy.
  destruct H3; SimpS.
  + apply IHc2 with (c':=c2'0) (c'':=x33) (t:=x0) in H11 ; try easy.
    destruct H11; SimpS.
    * left. split. easy.  constructor; Simpl.
    * right. exists {x,x3}. split; Simpl. split; try easy. apply dtrs1_imp_dtr1_d in H4.
      constructor; Simpl.
  + Simpl. eapply step0_mb_id' in H11.
     * SimpS. right. exists {x3,x4}. repeat split . Checkpure.
       constructor; Simpl.
     * exact H9.
     * exact H10.
- introv P1 P2 R H HT. Inverts R. unfold memBlock in HT. unfold lhsMB in HT.
  unfold rhsMB in HT. Invstep HT. SimpS.
  apply step_rhs in H16. SimpS.
  apply step_lhs with  (sav:=false) (rol:=false) (d:= d) (r:= r) (fai:=fbset2bool f) in H19; try easy.
  SimpS. simpl in H1.  rewrite s2bob2s in H1. Inverts H1. Inverts H7.
  case_eq((eqb d' x68)); intro Hyp1.
  + rewrite Hyp1 in H2. simpl in H2. rewrite rew_bool2bsetf in H2.
    unfold bool2bset in H2. simpl in H2.
    apply IHc with (c2':=x31) (c'':=x3) (t2:= {x0, x57, {x54, x55, x53}}) (s:={s, bool2bset d'}) (t:={t, x71})
                   (f:= f) in H6; Simpl. destruct H6; SimpS.
    * left. split; Simpl. constructor; Simpl. simpl. constructor.
    * right. exists x1. repeat split; Simpl. constructor; Simpl. constructor.
    * Checkpure.
    * assert (x68=d'). destruct x68; destruct d'; try Inverts Hyp1; try easy. Inverts H. Simpl.
    * Checkpure.
  + rewrite Hyp1 in H2. unfold bool2bset in H2. simpl in H2. Simpl.
    eapply step0_mb_id'  in H2.
    * Simpl. right. exists x1. repeat split; Simpl. constructor; Simpl. constructor.
    * exact H6.
    * exact H4.
  + rewrite rew_bool2bsetf; easy.
Qed.

(*Possible consequences of a glitch during odd clock cycle if before the state was correct*)
Lemma stepg0_mb : forall S T (c c' c'':circuit S T) c2 c2' t2 s t,
                   pure_bset s -> dtrs0 c c' c2
                -> step c' s t c''
                -> stepg c2 {s,{~0,~0,~0}} t2 c2'
                ->
  (                t2 = {t, {~0,~0,~0}}  /\ dtr1_r   c c' c'' c2' )  (*r is corrupted*)
\/(                t2 = {t, {~0,~0,~0}}  /\ dtr1_r'  c c' c'' c2' )  (*r' is corrupted*)
\/( (exists e1 e2, t2 = {e1,{~0,~0,e2}}) /\ dtr1_d   c c' c'' c2' )  (*glitch after d':fail is corupted(eg at comparator) and d*)
\/( (exists e1,    t2 = {t, {~0,~0,e1}}) /\ dtr1_d'  c c' c'' c2' ). (*glitch before d' kills d' and fail output*)
Proof.
intros S T c. induction c.
- introv P R H HT. Inverts R. Inverts H. Inverts HT; Dd_buset v; Inverts H10; Inverts H2.
  Inverts H. Inverts H7.
  + rewrite <- H. right. right. left. split; repeat constructor. Simpl.
  + rewrite <- H. right. right. left. split; repeat constructor. Simpl.
  + rewrite <- H0. right. right. left. split; repeat constructor. Simpl.
  + rewrite <- H0. right. right. left. split; repeat constructor. Simpl.
  + left. split; repeat constructor.
  + Inverts H. right. right. left. split; repeat constructor. Simpl.
- introv P R H HT. Inverts R. Inverts H. Inverts HT; Dd_buset v; Inverts H10. Inverts H.
  Inverts H2.
  + left. split. Simpl. constructor.
  + right. right. left. Inverts H. Inverts H2. split; repeat constructor. Simpl.
- introv P R H HT. Inverts R. Inverts H. Inverts HT. SimpS.
  + apply IHc1 with (c':=c1') (c'':= c1'0) (t:=t0 ) in H3; try easy.
    destruct H3 as [H|[H|[H|H]]]; SimpS.
    * apply step0_mb with (c:=c2) (c':=c2'0) (c'':=c2'1) (t:=t) in H12; try easy. SimpS.
      left. split; repeat constructor; apply dtrs1_imp_dtr1_r in H1; easy. Simpl.
    * apply step0_mb with (c:=c2) (c':=c2'0) (c'':=c2'1) (t:=t) in H12; try easy. SimpS.
      right. left. split; repeat constructor; apply dtrs1_imp_dtr1_r' in H1; easy. Simpl.
    * apply step0_mb_if with (c:=c2) (c':=c2'0) (c'':=c2'1) (t:=t) (s:=t0) in H12; try easy. SimpS.
      right. right. left. split; repeat constructor; Simpl.
    * apply step0_mb_f  with (c:=c2) (c':=c2'0) (c'':=c2'1) (t:=t)  in H12; try easy. SimpS.
      right. right. right. split; repeat constructor; Simpl; apply dtrs1_imp_dtr1_d' in H1; easy. Simpl.
  + apply step0_mb with (c:=c1) (c':=c1') (c'':=c1'0) (t:=t0) in H3; try easy. SimpS.
    apply IHc2 with (c':=c2'0) (c'':=c2'1) (t:=t ) in H12; Simpl.
    destruct H12 as [H|[H|[H|H]]]; SimpS.
    * left. split; repeat constructor; apply dtrs1_imp_dtr1_r in H0; easy.
    * right. left. split; repeat constructor; apply dtrs1_imp_dtr1_r' in H0; easy.
    * right. right. left. split; repeat constructor; Simpl; apply dtrs1_imp_dtr1_d in H0; try easy.
    * right. right. right.  split; repeat constructor;Simpl; apply dtrs1_imp_dtr1_d' in H0; easy.
-  introv P R H HT. Inverts R. Inverts H. unfold SWAP_LS in HT. unfold SWAP_LR in HT. Invstep HT;
    SimpS.
  + apply IHc1  with (c':=c1') (c'':=c1'0) (t:=t0) in H; try easy.
    destruct H as [H|[H|[H|H]]]; SimpS.
    * apply step0_mb with (c:=c2) (c':=c2'0) (c'':=c2'1) (t:=v) in H2; try easy. SimpS.
      left. split; repeat constructor; apply dtrs1_imp_dtr1_r in H2; easy.
    * apply step0_mb with (c:=c2) (c':=c2'0) (c'':=c2'1) (t:=v) in H2; try easy. SimpS.
      right. left. split; repeat constructor; apply dtrs1_imp_dtr1_r' in H2; easy.
    * apply step0_mb_f with (c:=c2) (c':=c2'0) (c'':=c2'1) (t:=v) in H2; try easy. SimpS.
      right. right. left. split; repeat constructor; Simpl; apply dtrs1_imp_dtr1_d in H2; easy.
    * apply step0_mb_f with (c:=c2) (c':=c2'0) (c'':=c2'1) (t:=v) in H2; try easy. SimpS.
      right. right. right. split; repeat constructor; Simpl; apply dtrs1_imp_dtr1_d' in H2; easy.
  + apply step0_mb with (c:=c1) (c':=c1') (c'':=c1'0) (t:=t0) in H; try easy. SimpS.
    apply IHc2 with  (c':=c2'0) (c'':=c2'1) (t:=v) in H1; try easy. destruct H1 as [H|[H|[H|H]]]; SimpS.
    * left. split; repeat constructor; apply dtrs1_imp_dtr1_r in H5; easy.
    * right. left. split; repeat constructor; apply dtrs1_imp_dtr1_r' in H5; easy.
    * right. right. left. split; repeat constructor; Simpl; apply dtrs1_imp_dtr1_d in H5; easy.
    * right. right. right. split; repeat constructor; Simpl; apply dtrs1_imp_dtr1_d' in H5; easy.
- introv P R H HT. Dd_buset t2. Inverts R. Inverts H7. Inverts H.
 Apply invstepgMBloop0 in HT. unfold mbgG in HT.
 destruct HT as [H|[H|[H|[H|H]]]].
 + unfold mbg02 in H. SimpS.
   apply step_rhs in H3.
   apply stepg0_lhs with (r'_O:=bool2bset r')  in H1; try easy. SimpS.
   destruct H1 as [[[H1|[H1|H1]] Hx2]|[H1 Hx2]]; SimpS;
   simpl in H; rewrite s2bob2s in H; Inverts H.
   * apply step0_mb_i with (c:=c) (c':=c'0) (c'':=c') (t:={t,a})
                               (s:={s, bool2bset x5}) in H0; try easy. SimpS.
     right. right. left. split; Simpl. repeat constructor. Simpl.
   * apply step0_mb_if with (c:=c) (c':=c'0) (c'':=c') (t:={t,a})
                                  (s:={s, bool2bset x5}) in H0; try easy. SimpS.
     right. right. left. split; Simpl. repeat constructor. Simpl.
   * apply step0_mb_f with (c:=c) (c':=c'0) (c'':=c') (t:={t,a})
                                (s:={s, bool2bset x5}) in H0; try easy. SimpS.
     right. right. right. split; Simpl. repeat constructor.
     apply dtrs1_imp_dtr1_d' in H0. easy. Checkpure.
   * apply step0_mb with (c:=c) (c':=c'0) (c'':=c') (t:={t,a})
                           (s:={s, bool2bset x5}) in H0; try easy. SimpS.
     right. left. split; Simpl. repeat constructor.
     apply dtrs1_imp_dtr1_r' in H0. easy. Checkpure.
 + unfold mbg03 in H. SimpS.
   apply step_rhs in H3.
   apply step_lhs with (sav:=false) (rol:=false) (d:= r)
                             (r:= r) (fai:=false) in H1; try easy. SimpS.
   simpl in H. rewrite s2bob2s in H. Inverts H.
   simpl in H0. rewrite eqb_reflx in H0. unfold bool2bset in H0. simpl in H0.
   apply IHc with (c':=c'0) (c'':=c') (t:={t,a}) in H0; try easy. SimpS.
   destruct H0 as [[H1 Hx2]| [Hx2|[H1|H1]]]; SimpS.
   * left. split; Simpl. repeat constructor. easy.
   * right. left. split; Simpl. repeat constructor. easy.
   * right. right. left. split; Simpl. repeat constructor. easy.
   * right. right. right. split; Simpl. repeat constructor. easy.
   * Checkpure.
 + unfold mbg06 in H. SimpS.
   apply step_lhs with(sav:=false) (rol:=false)
                            (d:= r) (r:= r) (fai:=false) in H1; try easy. SimpS.
   simpl in H0. rewrite eqb_reflx in H0. unfold bool2bset in H0. simpl in H0.
   apply step0_mb with (c:=c) (c':=c'0) (c'':=c') (t:={t,a})  in H0; try easy. SimpS.
   apply stepg_rhs with (si:=fbset2bool a) (sav2:= false) (sav:= false)
                           (fai:= false) (rol:=false) (r:=r) in H3; try easy. SimpS.
   destruct H3; SimpS.
   * left. split; Simpl. repeat constructor.
     apply dtrs1_imp_dtr1_r in H1.  easy.
   * left. split; Simpl. repeat constructor.
     apply dtrs1_imp_dtr1_r in H1. easy.
   * rewrite rew_bool2bsetf; Simpl.
   * Checkpure.
 + unfold mbg07 in H. destruct H; SimpS.
   apply step_rhs in H4. SimpS.
   Inverts H3. (*case: after invertion of introglitch*)
   * apply step_lhs_r with (sav:=false) (rol:=false)
                          (d:= r) (fai:=false) in H1; try easy. SimpS.
     simpl in H. simpl in H0. rewrite eqb_reflx in H0. unfold bool2bset in H0.
     simpl in H0. apply step0_mb with (c:=c) (c':=c'0) (c'':=c') (t:={t,a})in H0;
     try easy. SimpS. destruct H3; SimpS; left; split; Simpl; repeat constructor;
     apply dtrs1_imp_dtr1_r in H1; try easy. Checkpure.
   * symmetry in H4; destruct r; Inverts H4. unfold bool2bset in H1. simpl in H1.
     apply step_lhs_r with  (sav:=false) (rol:=false) (d:= true)  (fai:=false) in H1; try easy.
     simpl in H1. destruct H1; SimpS. simpl in H.  unfold bool2bset in H0. simpl in H0.
     apply step0_mb with (c:=c) (c':=c'0) (c'':=c') (t:={t,a}) in H0; try easy. SimpS.
     left. split; Simpl. destruct H3; SimpS; repeat constructor;
     apply dtrs1_imp_dtr1_r in H1; easy.
   * apply step_lhs with  (sav:=false) (rol:=false) (d:=r)
                                 (r:= r)   (fai:=false) in H1; try easy. SimpS.
     simpl in H. simpl in H0. rewrite eqb_reflx in H0. unfold bool2bset in H0.
     simpl in H0. apply step0_mb with (c:=c) (c':=c'0) (c'':=c') (t:={t,a})in H0;
     try easy. rewrite s2bob2s in H; Inverts H. SimpS.
     left. split; Simpl. repeat constructor;
     apply dtrs1_imp_dtr1_r in H0; easy. Checkpure.
 + unfold mbg08 in H. destruct H; SimpS.
   apply step_rhs in H4. SimpS.
   Inverts H3. (*case: after invertion of introglitch*)
   * apply step_lhs_i with (sav:=false) (rol:=false)
                          (r:= r) (fai:=false) in H1; try easy. SimpS.
     simpl in H. rewrite s2bob2s in H; Inverts H. simpl in H0. unfold bool2bset in H0.
     simpl in H0. apply step0_mb_f with (c:=c) (c':=c'0) (c'':=c') (t:={t,a})in H0;
     try easy. SimpS. destruct H3; SimpS; right; right; right; simpl; split; Simpl; repeat constructor;
     apply dtrs1_imp_dtr1_d' in H0; try easy. Checkpure.
   * symmetry in H4; destruct r; Inverts H4. unfold bool2bset in H1. simpl in H1.
     apply step_lhs_i with  (sav:=false) (rol:=false) (r:= true)  (fai:=false) in H1; try easy.
     simpl in H1. destruct H1; SimpS. simpl in H.  unfold bool2bset in H0. simpl in H0.
     apply step0_mb_f with (c:=c) (c':=c'0) (c'':=c') (t:={t,a}) in H0; try easy. SimpS.
     right. right. right. split; Simpl. destruct H3; SimpS; repeat constructor;
     apply dtrs1_imp_dtr1_d' in H0; easy.
   * apply step_lhs with  (sav:=false) (rol:=false) (d:= r)
                                 (r:= r)   (fai:=false) in H1; try easy. SimpS.
     simpl in H. simpl in H0. rewrite eqb_reflx in H0. unfold bool2bset in H0.
     simpl in H0. apply step0_mb with (c:=c) (c':=c'0) (c'':=c') (t:={t,a})in H0;
     try easy. rewrite s2bob2s in H; Inverts H. SimpS.
     left. split; Simpl. repeat constructor;
     apply dtrs1_imp_dtr1_r in H0; easy. Checkpure.
Qed.
