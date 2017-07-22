(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-  Properties of input buffers  

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import dtrTransform.

Set Implicit Arguments.

(* ------------------------------------------------------- *)

(* Definition of the input buffer is in dtrTransform        *)
(* Definition inpBufDTR (b b':bool):circuit (§ # §) § :=
   -|FORK-o--|ID, (Celb b) -o- (Celb b')|-,ID|--o-SWAP-o-Mux21.*)


(* ####################################################### *)
(** *     Properties of a single input Buffer              *)
(* ####################################################### *)

(** **                Normal mode   (rB=0)                 *)

Lemma step_ib : forall b1 b2 s t c, 
                     pure_bset s 
                  -> step (inpBufDTR b1 b2) {s,~0} t c 
                  -> t=s /\ c=inpBufDTR (fbset2bool s) b1.
Proof.
introv P H. 
assert (F:fstep (inpBufDTR b1 b2) {s,~0} = Some (s,inpBufDTR (fbset2bool s) b1)). 
destruct b1; destruct b2; Destruct_s s; destruct x; cbv; try Inverts P; easy.
Apply fstep_imp_detstep with F in H. SimpS. easy. 
Qed.


(** **        Potential glitch on the rb control wire     *)

Lemma step_ib_r : forall b1 b2 s t rb c, 
                   pure_bset s -> step (inpBufDTR b1 b2) {s,rb} t c 
                -> c=inpBufDTR (fbset2bool s) b1.
Proof.
introv P H. unfold inpBufDTR in H. unfold Celb in H. unfold Mux21 in H.
Invstep H. SimpS.
Apply fbset2bool_equiv in H18.
subst. easy.
Qed.


(** ** Property  when a glitch occurs within an input buffer  *)
(**                  (by reflection)                          *)

(* Property on the appropriate form for reflection tactics *)
(* p={b1,b2,s}, rb=0 *)

Lemma stepg_ib_R : forall p t c, 
                   ((fun p => pure_bset p) p)
                -> stepg ((fun p => inpBufDTR (fbset2bool (fstS(fstS p))) (fbset2bool (sndS (fstS p)))) p) 
                         ((fun p =>{sndS p,~0}) p) t c
                -> (fun e =>  (snd e=inpBufDTR (fbset2bool (sndS(fst(fst e))))
                                               (fbset2bool (fstS(fstS(fst(fst e))))))
                           \/ (snd(fst e)=sndS(fst(fst e))
                                /\  (snd e=inpBufDTR (fbset2bool (sndS(fst(fst e)))) true  
                                  \/ snd e=inpBufDTR (fbset2bool (sndS(fst(fst e)))) false))) (p,t,c).
Proof. introv. Reflo_step_g. Qed. 

(* Property in the standard (and more readable) form *)

Lemma stepg_ib : forall b1 b2 s t c, 
                 pure_bset s -> stepg (inpBufDTR b1 b2) {s,~0} t c 
              -> c=inpBufDTR (fbset2bool s) b1
              \/ (t=s /\ exists b', c=inpBufDTR (fbset2bool s) b').
Proof.
introv P H.
set (p := {bool2bset b1,bool2bset b2,s}).
assert (X1: fbset2bool (fstS (fstS p)) = b1)
   by (replace p with {bool2bset b1,bool2bset b2,s}; destruct b1; easy).
assert (X2: fbset2bool (sndS (fstS p)) = b2)
   by (replace p with {bool2bset b1,bool2bset b2,s}; destruct b2; easy).
rewrite <- X1 in H. rewrite <- X2 in H. 
Apply stepg_ib_R in H.
destruct H as [H|[H [H1|H1]]].  
- left. destruct b1; easy.
- right. split. easy.
  exists true. easy.
- right. split. easy. 
  exists false. easy.
Qed.


(** **              Recovery mode  (rB=1)                 *)

Lemma step12_ib : forall b1 b2 s t c, 
                    pure_bset s 
                 -> step (inpBufDTR b1 b2) {s,~1} t c 
                 -> t=bool2bset b2 /\ c=inpBufDTR (fbset2bool s) b1.
Proof.
introv P H. 
assert (F:fstep (inpBufDTR b1 b2) {s,~1} = Some (bool2bset b2,inpBufDTR (fbset2bool s) b1)). 
destruct b1; destruct b2; Destruct_s s; destruct x; cbv; try Inverts P; easy.
eapply fstep_imp_detstep in F; Simpl. 
Qed.


(* ####################################################### *)
(** *         Input Buffer Bank Properties                 *)
(**  Only properties used outside                          *)
(**  By induction on the type (of the primary inputs)      *)
(* ####################################################### *)

(** **                Normal mode   (rB=0)                 *)

Lemma step_ibs : forall S (s1 s2 s t:{|S|}) c, 
                      pure_bset s1 -> pure_bset s2 -> pure_bset s 
                   -> step (dtrIB_T s1 s2) {s,~0} t c
                   -> t=s /\ c=dtrIB_T s s1.
Proof.
introv P1 P2 P H. induction S.
- cbn in H. apply step_ib in H; easy.
- Dd_buset_all. cbn in H. 
  Invstep H. apply fact_shuffle in H1. SimpS.
  Apply IHS1 in H0.
  Apply IHS2 in H2.
  SimpS; easy.
Qed.


(** **        Potential glitch on the rb control wire     *)

Lemma step_ib_rs : forall S (s1 s2 s t:{|S|}) rb c, 
                    pure_bset s1 -> pure_bset s2 -> pure_bset s 
                 -> step (dtrIB_T s1 s2) {s,rb} t c 
                 -> c=dtrIB_T s s1.

Proof.
introv P1 P2 P H. induction S.
- cbn in H. apply step_ib_r in H; SimpS; easy.   
- Dd_buset_all. cbn in H. 
  Invstep H. apply fact_shuffle in H1. SimpS.
  Apply IHS1 in H0.
  Apply IHS2 in H2.
  SimpS. easy.
Qed.


(** **          Recovery mode  (rB=1)                  *)

Lemma step12_ibs : forall S (s1 s2 s t:{|S|}) c, 
                     pure_bset s1 -> pure_bset s2 -> pure_bset s 
                  -> step (dtrIB_T s1 s2) {s,~1} t c 
                  -> t=s2 /\ c=dtrIB_T s s1.
Proof.
introv P1 P2 P H. induction S.
- cbn in H. apply step12_ib in H; SimpS; try easy.
  split. Apply b2bs_equiv_fb2bs. easy.
- Dd_buset_all. cbn in H. 
  Invstep H. apply fact_shuffle in H1. SimpS.
  Apply IHS1 in H0.
  Apply IHS2 in H2.
  SimpS. easy.
Qed.



(** ** Property of the input buffer bank when a glitch occurs within   *)

Lemma stepg_ibs : forall S (s1 s2 s t:{|S|}) c,
                  pure_bset s1 -> pure_bset s2 -> pure_bset s 
               -> stepg (dtrIB_T s1 s2) {s,~0} t c
               -> c=dtrIB_T s s1
               \/ (t=s /\ exists s', c=dtrIB_T s s' /\ pure_bset s').
Proof.
introv P1 P2 P H. induction S.
- cbn in H. Apply stepg_ib in H; SimpS. 
  destruct H as [H|H].
  + left. easy. 
  + right. SimpS. split. easy. 
    exists (bool2bset x). destruct x; easy.
- Dd_buset_all. cbn in H. 
  apply inv_stepgS1 in H; try (solve[repeat constructor]). SimpS.
  Invstep H; apply fact_shuffle in H0; SimpS.
  + Apply IHS1 in H1.
    Apply step_ibs in H8. SimpS.
    destruct H1 as [H | [H1 [s' H]]]; SimpS.
    * left. easy.
    * right. split. easy. exists {s',x10}. easy.
  + Apply step_ibs in H1.
    Apply IHS2 in H8. SimpS.    
    destruct H8 as [H | [H1 [s' H]]]; SimpS.
    * left. easy.
    * right. split. easy. exists {x9,s'}. easy.
Qed.

