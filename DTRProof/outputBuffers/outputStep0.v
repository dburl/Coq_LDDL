(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-   Basic properties of output buffers when the control block
    is in state 0.

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import dtrTransform outputStep.

Set Implicit Arguments.


(* ####################################################### *)
(** *     Output Buffer Properties                         *)
(* ####################################################### *)

(** **          Normal mode   (roolBack=0, subst=0)        *)


(* Odd cycles for all possible (save, fail, rollBack) (subst=0) *)
Lemma step0_ob_sbf : forall a b b' save rb fail t c, 
                      step (outBufDTR b b b b b') {bool2bset a,{save,rb,fail,~0}} t c 
                   -> t={{bool2bset b,{bool2bset b,bool2bset b'}},fail}
                   /\ c=outBufDTR a b a b b.
Proof. 
introv H.
assert (F:fstep (outBufDTR b b b b b') {bool2bset a,{save,rb,fail,~0}} 
        = Some ({{bool2bset b,{bool2bset b,bool2bset b'}},fail},outBufDTR a b a b b)) 
    by (destruct b; destruct b'; destruct a; Destruct_s fail; destruct x; 
        Destruct_s rb; destruct x; Destruct_s save; destruct x; vm_compute; easy).
eapply fstep_imp_detstep in F; SimpS; eauto.  
Qed.

(* Odd cycles for all possible (save, fail, subst) (roolBack=0) *)

Lemma step0_ob_sfu : forall a b b' save fail subst t c, 
                    step (outBufDTR b b b b b') {bool2bset a,{save,~0,fail,subst}} t c 
                 -> t={{bool2bset b,{bool2bset b,bool2bset b'}},fail}
                  /\ c=outBufDTR a b a b b.
Proof. 
introv H.
assert (F:fstep (outBufDTR b b b b b') {bool2bset a,{save,~0,fail,subst}} 
        = Some ({{bool2bset b,{bool2bset b,bool2bset b'}},fail},outBufDTR a b a b b)) 
    by (destruct b; destruct b'; destruct a; Destruct_s fail; destruct x; 
        Destruct_s subst; destruct x; Destruct_s save; destruct x; vm_compute; easy).
eapply fstep_imp_detstep in F; SimpS; eauto.  
Qed.


(** Property of output buffer when a glitch occurs within  *)
(**  Odd cycle and subst = ? *)

Lemma step0_ob_u : forall a b p t f c, 
                        step (outBufDTR a a a a b) {bool2bset p,{~0,~0,bool2bset f,~?}} t c 
                     -> t={{bool2bset a,{bool2bset a,bool2bset b}},bool2bset f}
                     /\ c=outBufDTR p a p a a.
Proof.
introv H.
assert (F:fstep (outBufDTR a a a a b) {bool2bset p,{~0,~0,bool2bset f,~?}} 
        = Some ({{bool2bset a,{bool2bset a,bool2bset b}},bool2bset f},outBufDTR  p a p a a)) 
    by (destruct b; destruct p; destruct f; destruct a; vm_compute; try easy).
eapply fstep_imp_detstep in F; Simpl.  
Qed.


(* ####################################################### *)
(** *     Output Buffer Bank Properties                     *)
(* ####################################################### *)

(** **                Normal mode   (rB=0)                 *)


Lemma step0_obs_sbf : forall S (p p' s :{|S|}) save rb fail  t c, 
                       pure_bset p -> pure_bset p' -> pure_bset s 
                    -> step (dtrOB_T p p p p p') {s,{save,rb,fail,~0}} t c 
                    -> t={{p,{p,p'}},fail} 
                    /\ c=dtrOB_T s p s p p.
Proof.
introv P1 P2 P H. induction S.
- cbn in H.
  assert (H1: exists b,  bool2bset b = s) by (apply pure_imp_exbool; easy).
  destruct H1 as [b H1]. subst.
  apply step0_ob_sbf in H; try easy. Simpl.
  Destruct_s p; destruct x; Inverts P1; 
  Destruct_s p'; destruct x; Inverts P2; destruct b; try easy.
- Dd_buset_all. cbn in H. 
  Invstep H. apply fact_plug1_OB in H. apply fact_plug2_OB in H3.
  apply fact_plug3_OB in H2. SimpS. 
  apply IHS1 in H7; try easy. SimpS.
  apply IHS2 in H4; try easy. Simpl. 
Qed.


(* Even cycles for all possible (save, fail, subst) (roolBack=0) *)

Lemma step0_obs_sfu :forall S (p p' s :{|S|})save fail subst t c, 
                       pure_bset p -> pure_bset p' -> pure_bset s 
                    -> step (dtrOB_T p p p p p') {s,{save,~0,fail,subst}} t c 
                    -> t={{p,{p,p'}},fail} 
                    /\ c=dtrOB_T s p s p p.
Proof.
introv P1 P2 P H. induction S.
- cbn in H.
  assert (H1: exists b,  bool2bset b = s) by (apply pure_imp_exbool; easy).
  destruct H1 as [b H1]. subst.
  apply step0_ob_sfu in H; try easy. Simpl.
  Destruct_s p; destruct x; Inverts P1; 
  Destruct_s p'; destruct x; Inverts P2; destruct b; try easy.
- Dd_buset_all. cbn in H. 
  Invstep H. apply fact_plug1_OB in H.  apply fact_plug2_OB in H3.
  apply fact_plug3_OB in H2. SimpS. 
  apply IHS1 in H7; try easy. SimpS.
  apply IHS2 in H4; try easy. Simpl.
Qed.




(* Even cycles subst = ? *)
Lemma step0_obs_u :forall S (p p' a:{|S|}) f t c, 
                     pure_bset p -> pure_bset p' -> pure_bset a 
                  -> step (dtrOB_T p p p p p') {a,{~0,~0,bool2bset f,~?}} t c 
                  -> t={{p,{p,p'}},bool2bset f} 
                  /\ c=dtrOB_T a p a p p.
Proof. 
induction S; introv P1 P2 P3 H.
- cbn in H. 
  assert (H1: a = bool2bset(fbset2bool a))
  by (Destruct_s a; destruct x; Inverts P3; easy).
  rewrite H1 in H; clear H1.
  apply step0_ob_u in H; try easy. Simpl.
  repeat (rewrite rew_bool2bsetf; try easy).
- Dd_buset_all. cbn in H. 
  Invstep H. apply fact_plug1_OB in H.  
  apply fact_plug2_OB in H3.
  apply fact_plug3_OB in H2. SimpS. 
  apply IHS1 in H7; try easy. SimpS.
  apply IHS2 in H4; try easy. Simpl. 
Qed. 


(* State 0 - Effect of a corrupted input and a glitch on rollback  *)


Lemma step0_obs_b : forall S (p p' z:{|S|}) t c, 
                        pure_bset p -> pure_bset p' 
                     -> step (dtrOB_T p p p p p') {z,{~0,~?,~0,~0}} t c 
                     ->  t={{p,{p,p'}},~0}
                     /\ (exists x y, pure_bset x /\ pure_bset y /\ c=dtrOB_T x p y p p).
Proof. 
induction S; introv P1 P2 H.
- cbn in H.
  apply step_ob_ibf in H; try easy. SimpS. split.
  + Destruct_s p; destruct x; Inverts P1; 
    Destruct_s p'; destruct x; Inverts P2; easy.
  + exists (bool2bset x) (bool2bset x0).
    unfold dtrOB_T. repeat rewrite rew_fbset2bool. 
    repeat split; CheckPure; easy.
- Dd_buset_all. cbn in H.
  Invstep H. SimpS. 
  apply fact_plug1_OB in H. apply fact_plug2_OB in H3.
  apply fact_plug3_OB in H2. SimpS. 
  eapply IHS1 in H7; try easy. SimpS.
  apply IHS2 in H4; try CheckPure. SimpS. 
  split. easy.
  exists {x,x1} {x0,x2}. easy.
Qed.
