(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
--   General properties of memory blocks 

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)
(*Add LoadPath "..\..\Common\".
	Require Import CirReflect. 
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\". *)
Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Export dtrTransform relationPred.

Set Implicit Arguments.
(* ###################################################################### *)
(** General properties of Memory Block                                    *)
(* ###################################################################### *)

Lemma transf_dtr0 : forall S T (c:circuit S T) c2,  dtrMemT c = c2 <-> dtrs0 c c c2.
Proof.
split; introv H; unfold dtrs0.
- induction c ; rewrite <- H; try easy. repeat constructor. easy.
- induction c; Inverts H; try easy.
  + apply IHc1 in H4. apply IHc2 in H9. subst. easy.
  + apply IHc1 in H3. apply IHc2 in H10. subst. easy.
  + apply IHc in H5. Inverts H8. Simpl. 
Qed. 


(** Being in a state implies being in the corresponding (possibly) more corrupted state *)

(** For state 0 *)
Lemma dtrs0_imp_dtr0_d' : forall S T (c c' :circuit S T) c2, 
                           dtrs0 c c' c2 -> dtr0_d' c c' c2.
Proof.
introv H. induction H; try (constructor; easy). Inverts H0.
Inverts H; repeat constructor; try easy; try Inverts IHdtr0;
Simpl.
Qed.

Lemma dtrs0_imp_dtr0_d : forall S T (c c':circuit S T) c2, 
                           dtrs0 c c' c2 -> dtr0_d c c' c2.
Proof.
introv H. induction H; try (constructor; easy). Inverts H0.
Inverts H; repeat constructor; try easy; try Inverts IHdtr0;
Simpl. 
Qed.

Lemma dtrs0_imp_dtr0_r : forall S T (c c':circuit S T) c2, 
                          dtrs0 c c'  c2 -> dtr0_r c c'  c2.
Proof.
introv H. induction H; try (constructor; easy). Inverts H0.
Inverts H; repeat constructor; try easy; try Inverts IHdtr0;
Simpl. 
Qed.

Lemma dtrs0_imp_dtr0_r' : forall S T (c c' :circuit S T) c2, 
                           dtrs0 c c'  c2 -> dtr0_r' c c'  c2.
Proof.
introv H. induction H; try (constructor; easy). Inverts H0.
Inverts H; repeat constructor; try easy; try Inverts IHdtr0;
Simpl.   
Qed.

Lemma dtrs0_imp_dtr0_dr : forall S T (c c' :circuit S T) c2, 
                           dtrs0 c c'  c2 -> dtr0_dr c c'  c2.
Proof.
introv H. induction H; try (constructor; easy). Inverts H0.
Inverts H; repeat constructor; try easy; try Inverts IHdtr0;
Simpl.  
Qed.


Lemma dtr0_d_imp_dr : forall S T (c c':circuit S T) c2, 
                           dtr0_d c c' c2 -> dtr0_dr c c' c2.
Proof.
introv H. induction H; try (constructor; easy).
Inverts H; try Inverts IHdtr0; try Inverts H0; repeat constructor; Simpl. 
Qed.

(** For state 1 *)

Lemma dtr1_r_imp_d'r : forall S T (c c' c'':circuit S T) c2, 
                        dtr1_r c c' c'' c2 -> dtr1_d'r c c' c'' c2.
Proof.
introv H. induction H; try (constructor; easy).
Inverts H0. repeat constructor; easy. 
Qed.

Lemma dtr1_r_imp_rr' : forall S T (c c' c'':circuit S T) c2, 
                        dtr1_r c c' c'' c2 -> dtr1_rr' c c' c'' c2.
Proof.
introv H. induction H; try (constructor; easy).
Inverts H0. repeat constructor; easy. 
Qed.


Lemma dtrs1_imp_dtr1_d : forall S T (c c' c'':circuit S T) c2, 
                           dtrs1 c c' c'' c2 -> dtr1_d c c' c'' c2.
Proof.
introv H. induction H; try (constructor; easy). Inverts H0.
Inverts H; repeat constructor; try easy; try Inverts IHdtr1; Simpl. 
Qed.

Lemma dtrs1_imp_dtr1_d' : forall S T (c c' c'':circuit S T) c2, 
                           dtrs1 c c' c'' c2 -> dtr1_d' c c' c'' c2.
Proof.
introv H. induction H; try (constructor; easy). Inverts H0.
Inverts H; repeat constructor; try easy; try Inverts IHdtr1; Simpl. 
Qed.

Lemma dtrs1_imp_dtr1_r : forall S T (c c' c'':circuit S T) c2, 
                           dtrs1 c c' c'' c2 -> dtr1_r c c' c'' c2.
Proof.
introv H. induction H; try (constructor; easy). Inverts H0.
Inverts H; repeat constructor; try easy; try Inverts IHdtr1; Simpl.  
Qed.

Lemma dtrs1_imp_dtr1_r' : forall S T (c c' c'':circuit S T) c2, 
                           dtrs1 c c' c'' c2 -> dtr1_r' c c' c'' c2.
Proof.
introv H. induction H; try (constructor; easy). Inverts H0.
Inverts H; repeat constructor; try easy; try Inverts IHdtr1; Simpl. 
Qed.


Lemma dtrs1_imp_dtr1_d'r : forall S T (c c' c'':circuit S T) c2, 
                           dtrs1 c c' c'' c2 -> dtr1_d'r c c' c'' c2.
Proof.
introv H. induction H; try (constructor; easy). Inverts H0.
Inverts H; repeat constructor; try easy; try Inverts IHdtr1; Simpl. 
Qed.


Lemma dtr1_d'_imp_d'r : forall S T (c c' c'':circuit S T) c2, 
                           dtr1_d' c c' c'' c2 -> dtr1_d'r c c' c'' c2.
Proof.
introv H. induction H; try (constructor; easy). Inverts H0.
Inverts H; repeat constructor; try easy; try Inverts IHdtr1; Simpl. 
Qed.

(** For recovery states *)

Lemma dtrec_rr'_imp_d'rr' : forall S T (c c':circuit S T) c2, 
                          dtrec_rr' c c' c2 -> dtrec_d'rr' c c' c2.
Proof.
introv H. induction H; try (constructor; easy). Inverts H0.
Inverts H; repeat constructor; try easy; 
try Inverts IHdtr0; try Inverts H0; try constructor; eauto. 
Qed.