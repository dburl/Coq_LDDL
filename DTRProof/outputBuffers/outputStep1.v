(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-   Basic properties of output buffers when the control block
    is in state 1.

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


(* Even  cycles for all possible (save, fail, rollBack) (subst=0) *)
Lemma step1_ob_sbf : forall b b' save rb fail t c, 
                    step (outBufDTR b b' b b' b') {bool2bset b,{save,rb,fail,~0}} t c 
                 -> exists f, t={{bool2bset b',{bool2bset b',bool2bset b'}},f}
                  /\ c=outBufDTR b b b b b'.
Proof. 
introv H.
assert (F:fstep  (outBufDTR b b' b b' b') {bool2bset b,{save,rb,fail,~0}} 
        = Some ({{bool2bset b',{bool2bset b',bool2bset b'}},orS {fail,(bool2bset(negb(eqb b b')))}},
                outBufDTR b b b b b')) 
    by (destruct b; destruct b'; Destruct_s fail; destruct x;  
        Destruct_s rb; destruct x; Destruct_s save; destruct x; vm_compute; easy).
exists (orS {fail, bool2bset (negb (eqb b b'))}).
eapply fstep_imp_detstep in F; Simpl.
Qed.

(** Property of output buffer when a glitch occurs within  *)
(**  Even cycle and subst = ? *)

Lemma step1_ob_u : forall a b t f c, 
                        step (outBufDTR a b a b b) {bool2bset a,{~1,~0,bool2bset f,~?}} t c 
                     -> t={{bool2bset b,{bool2bset b,bool2bset b}},bool2bset(orb f (xorb a b))}
                     /\ c=outBufDTR a a a a b.
Proof. 
introv H.
assert (F:fstep (outBufDTR a b a b b) {bool2bset a,{~1,~0,bool2bset f,~?}} 
        = Some ({{bool2bset b,{bool2bset b,bool2bset b}},bool2bset(orb f (xorb a b))},outBufDTR  a a a a b)) 
    by (destruct b; destruct f; destruct a; vm_compute; easy).
eapply fstep_imp_detstep in F; Simpl.
Qed. 


(* ####################################################### *)
(** *     Output Buffer Bank Properties                     *)
(* ####################################################### *)

(** **                Normal mode   (rB=0)                 *)



(* Even cycles for all possible (save, fail, rollBack) (subst=0) *)
Lemma step1_obs_sbf : forall S (p p' :{|S|}) save rb fail  t c, 
                      pure_bset p -> pure_bset p' 
                   -> step (dtrOB_T p p' p p' p') {p,{save,rb,fail,~0}} t c 
                   -> exists f, t={{p',{p',p'}},f} 
                   /\ c=dtrOB_T p p p p p'.
Proof.
induction S; introv P1 P2 H.
- cbn in H. 
  assert (H1: p = bool2bset(fbset2bool p))
  by (Destruct_s p; destruct x; Inverts P1; easy).
  rewrite H1 in H at 3; clear H1.
  apply step1_ob_sbf in H; try easy. Simpl.
  exists x2.
  Destruct_s p; destruct x; Inverts P1;
  Destruct_s p'; destruct x; Inverts P2; try easy.
- Dd_buset_all. cbn in H. 
  Invstep H. apply fact_plug1_OB in H.  apply fact_plug2_OB in H3.
  apply fact_plug3_OB in H2. SimpS. 
  apply IHS1 in H7; try easy. SimpS.
  apply IHS2 in H4; try easy. Simpl. 
Qed.

(* Even cycles subst = ? *)
Lemma step1_obs_u :forall S (p p':{|S|}) f t c, 
                     pure_bset p -> pure_bset p' 
                  -> step (dtrOB_T p p' p p' p') {p,{~1,~0,bool2bset f,~?}} t c
                  -> exists f, t={{p',{p',p'}},bool2bset f} 
                  /\ c=dtrOB_T p p p p p'.
Proof.
induction S; introv P1 P2 H.
- cbn in H. 
  assert (H1: p = bool2bset(fbset2bool p))
  by (Destruct_s p; destruct x; Inverts P1; easy).
  rewrite H1 in H at 3; clear H1.
  apply step1_ob_u in H; try easy. Simpl.
  repeat (rewrite rew_bool2bsetf; try easy).
  exists (f || xorb (fbset2bool p) (fbset2bool p')).
  split. easy. 
  Destruct_s p; destruct x; Inverts P1;
  Destruct_s p'; destruct x; Inverts P2; try easy.
- Dd_buset_all. cbn in H.
  Invstep H. apply fact_plug1_OB in H.
  apply fact_plug2_OB in H3.
  apply fact_plug3_OB in H2. SimpS.
  apply IHS1 in H7; try easy. SimpS.
  apply IHS2 in H4; try easy. Simpl.
Qed.



(* State 1 - Effect of a corrupted input and a glitch on rollback  *)

Lemma step1_obs_b : forall S (p p' z:{|S|}) f t c, 
                        pure_bset p -> pure_bset p' -> pure_bset f
                     -> step (dtrOB_T p p' p p' p') {z,{~1,~?,f,~0}} t c 
                     -> (exists f', t={{p',{p',p'}},bool2bset f'})
                     /\ (exists x y, pure_bset x /\ pure_bset y /\ c=dtrOB_T x p y p p').
Proof. 
induction S; introv P1 P2 P3 H.
- cbn in H.
  Apply step_ob_ibf in H. SimpS. split.
  + repeat (rewrite rew_bool2bsetf; try easy).
    Destruct_s p; destruct x; Inverts P1; 
    Destruct_s p'; destruct x; Inverts P2;
    Destruct_s f; destruct x; Inverts P3;
    try (exists false; easy); try (exists true; easy).
  + exists (bool2bset x) (bool2bset x0).
    subst. unfold dtrOB_T. repeat rewrite rew_fbset2bool.
    repeat split; CheckPure; easy.
- Dd_buset_all. cbn in H.
  Invstep H. SimpS.
  apply fact_plug1_OB in H. apply fact_plug2_OB in H3. apply fact_plug3_OB in H2.
  SimpS. Apply IHS1 in H7. SimpS.
  Apply IHS2 in H4. SimpS. split.
  + exists x4. easy.
  + exists {x,x2} {x0,x3}. easy.
Qed.
