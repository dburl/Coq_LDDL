(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-   states transitions without any glitches for memoty block

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import dtrTransform relationPred leftStep rightStep leftStepg.

Set Implicit Arguments.

(* ##################################################################### *)
(** Properties of Memory Block w/o Glitches for both cycles              *)
(* ##################################################################### *)

(** Basic properties of evaluation of DTR circuits without faults  *)

(*Odd cycles when all control signals (save, fail, rollBack) are zeros*)
Lemma step0_mb: forall S T (c c' c'':circuit S T) c2 c2' t2 s t, 
                pure_bset s -> dtrs0 c c' c2 
             -> step c' s t c''
             -> step c2 {s,{~0,~0,~0}} t2 c2'
             -> t2 = {t,{~0,~0,~0}} /\ dtrs1 c c' c'' c2'.
Proof.
introv P R H HT. induction H; unfold dtrs1.
- Inverts R. Invstep HT. Simpl.
- Inverts R. Invstep HT. Simpl.
- destruct c; Inverts R; Inverts HT; Simpl.
  Apply IHstep1 in H6; Simpl.
  Apply IHstep2 in H12; Simpl.
- Dd_buset t2. Inverts R. 
  unfold SWAP_LS in HT. unfold SWAP_LR in HT.
  Invstep HT. SimpS.
  Apply IHstep1 in H0; Simpl.
  Apply IHstep2 in H11; Simpl.
  repeat constructor; easy.
- Dd_buset t2. Inverts R. Inverts H8.
  unfold memBlock in HT. unfold lhsMB in HT. unfold rhsMB in HT.
  Invstep HT. SimpS.
  Apply step_rhs in H16. SimpS.
  apply step_lhs with (d:=r) (r:=r) (sav:=false) (rol:=false) (fai:=false) in H19; Simpl.
  unfold bool2bset in H2. repeat rewrite eqb_reflx in H2. cbn in H2.
  Apply IHstep in H2; Simpl. cbn in H1.
  rewrite s2bob2s in H1.
  repeat constructor; Simpl. cbn. constructor.
Qed.

(*Even cycles when the control signals (save, fail, rollBack) = {1,0, unknown not glitched}*)
Lemma step1_mb : forall S T (c c' c'':circuit S T) c2 c2' t2 s t f, 
                    pure_bset s ->  pure_bset f -> dtrs1 c c' c'' c2 
                    -> step c' s t c''
                    -> step c2 {s,{~1,~0,f}} t2 c2'
                    -> (exists b, t2 = {t,{~1,~0,bool2bset b}}) /\ dtrs0 c' c'' c2'.
Proof.
intros S T c. 
induction c; introv P1 P2 R H HT; unfold dtrs1; Inverts R.
- Invstep HT. Invstep H1. split; Simpl; try constructor.
  exists (fbset2bool f). rewrite rew_bool2bsetf; easy.
- Invstep HT. Invstep H1. split; Simpl; try constructor.
  exists (fbset2bool f). rewrite rew_bool2bsetf; easy.
- Inverts H. Invstep HT. Simpl.
  apply IHc1 with (c':=c1') (c'':= c1'') (t:=t0) in H; Simpl.
  apply IHc2 with (c':=c2'0) (c'':=c2'') (t:=t) in H0; Simpl.
  split; Simpl. constructor; easy.
- unfold  SWAP_LR in HT. unfold  SWAP_LS in HT.
  Invstep HT. SimpS. Inverts H13.
  Apply IHc1 with H H0 H1 H2 in H3. SimpS.
  Apply IHc2 with H1 H10 H11 in H9.
  split; Simpl. constructor; easy.
- Inverts H8. unfold memBlock in HT. unfold lhsMB in HT.
  unfold rhsMB in HT. Invstep HT.
  Inverts H20. SimpS.
  Apply step_rhs in H15.
  apply step_lhs with (fai:= fbset2bool f) (sav:=true) 
                      (rol:= false) (d:= x87) (r:= r) in H18; try rewrite rew_bool2bsetf; try easy.
  SimpS. cbn in H1.
  rewrite eqb_reflx in H2. unfold bool2bset in H2. cbn in H2.
  Apply  IHc with H4 H7 in H2.
  destruct H2; Simpl. split.
  + exists x. easy.
  + cbn. repeat constructor; easy.
Qed.
