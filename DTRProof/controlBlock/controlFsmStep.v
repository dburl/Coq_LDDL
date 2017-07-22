(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-   states of ctr block and their transition properties 
          Dmitry Burlyaev - Pascal Fradet - 2015  
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)
(*Add LoadPath "..\..\Common\".
Require Import CirReflect . 
Add LoadPath "..\..\TMRProof\".
Require Import tmrDef.
Add LoadPath "..\".
*)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import dtrTransform.

Set Implicit Arguments.

(* ####################################################### *)
(**       Basic properties of DTR control block  - SINGLE NON-REDUNDANT VERSION  *)
(* ####################################################### *)
(* Input: failM_out -> Outputs:  ((save # rollBack) # fail)) # rB) # subst  *)

(*Properties about the state transitions of the FSM*)

(*Normal mode: If the current binary encoded state is '000', 
               the next is '001' with the corresponding output *)
Lemma fact_stepCtrBl_12 : forall fI t c, step (ctrBl_dtr false false false) fI t c 
                                     -> t={~0,~0,~0,~0,~0} /\ c=(ctrBl_dtr false false true).
Proof.
introv H. assert (F:fstep (ctrBl_dtr false false false) fI 
                  = Some ({~0,~0,~0,~0,~0}, ctrBl_dtr false false true)) by
(Destruct_s fI ; destruct x; vm_compute; easy).
eapply fstep_imp_detstep in F; Simpl.
Qed.

(*Normal mode: If the current binary encoded state is '001' and no fail signal, 
               the next is '000' with the corresponding output *)
Lemma fact_stepCtrBl_21 : forall t c, step (ctrBl_dtr false false true) (~0) t c 
                                     -> t={~1,~0,~0,~0,~0} /\ c=(ctrBl_dtr false false false).
Proof.
introv H. assert (F:fstep (ctrBl_dtr false false true ) (~0) (*input fail =0 - no errors*)
                  = (Some ({~1,~0,~0,~0,~0},ctrBl_dtr  false false false ))) by (vm_compute; easy).
eapply fstep_imp_detstep in F; Simpl.
Qed.

(*Error detection: If the current binary encoded state is '001' and a fail signal=1, 
                   the recovery process starts with the next state '010' *)
Lemma fact_stepCtrBl_23 : forall t c, step (ctrBl_dtr false false true) (~1) t c 
                                      -> t={~1,~1,~1,~1,~1} /\ c=(ctrBl_dtr false true false).
Proof.
introv H. assert (F:fstep (ctrBl_dtr false false true ) (~1) (*input fail =1 - Error detected*)
              = (Some ({~1,~1,~1,~1,~1}, ctrBl_dtr  false true false ))) by (vm_compute; easy).
eapply fstep_imp_detstep in F; Simpl. 
Qed.

(*Recovery: If the current binary encoded state is '010', the next recovery state is '011' *)
Lemma fact_stepCtrBl_34 : forall fI  t c, step (ctrBl_dtr false true false) fI  t c 
                                     -> t={~0,~1,~1,~1,~1} /\ c=(ctrBl_dtr false true true).
Proof.
introv H. assert (F:fstep (ctrBl_dtr false true false ) fI (*input fail =1 - Error detected*)
              = (Some ({~0,~1,~1,~1,~1}, ctrBl_dtr  false true true ))) by
(Destruct_s fI ; destruct x;  vm_compute; easy).
eapply fstep_imp_detstep in F; Simpl.
Qed.

(*Recovery: If the current binary encoded state is '011' , the  next recovery state is '100' *)
Lemma fact_stepCtrBl_45 : forall fI  t c,   step (ctrBl_dtr  false true true) fI  t c 
                                          -> t={~0,~1,~0,~0,~1} /\ c=(ctrBl_dtr true false false ).
Proof.
introv H. assert (F:fstep (ctrBl_dtr  false true true) fI (*input fail =1 - Error detected*)
              = (Some ({~0,~1,~0,~0,~1}, ctrBl_dtr   true false false  ))) by
(Destruct_s fI ; destruct x;  vm_compute; easy).
eapply fstep_imp_detstep in F; Simpl.
Qed.
 
(*Return to normal mode: If the current binary encoded state is '101' , the  recovery state is normal '000' *)
Lemma fact_stepCtrBl_61 : forall fI  t c,   step (ctrBl_dtr true false true ) fI  t c 
                                     -> t={~1,~0,~0,~0,~0} /\ c=(ctrBl_dtr false false false).
Proof.
introv H. assert (F:fstep (ctrBl_dtr true false true  ) fI (*input fail =1 - Error detected*)
              = (Some ({~1,~0,~0,~0,~0}, ctrBl_dtr   false false false  ))) by
(Destruct_s fI ; destruct x;  vm_compute; easy).
eapply fstep_imp_detstep in F; Simpl. 
Qed.

(*Supporting property: if three redundant inputs are the same in the voting sub-circuit ctrVoting of
  control block- then the output equals to them and the returning circuit is statelss voting sub-circtuit ctrVoting*)
Lemma votNorm: forall s t c', step ctrVoting {s, s, s} t c' -> pure_bset s-> t=s /\c'=ctrVoting.
Proof.
introv H. Destruct_s s; Destruct_s x; Destruct_s x; Destruct_s x;
Destruct_s x; Destruct_s y2 ; Destruct_s y1; Destruct_s y0; Destruct_s y.
assert (F:fstep ctrVoting {~ x, ~ x0, ~ x1, ~ x2, ~ x3, {~ x, ~ x0, ~ x1, ~ x2, ~ x3}, {~ x, ~ x0, ~ x1, ~ x2, ~ x3}}
                 = (Some ({~ x, ~ x0, ~ x1, ~ x2, ~ x3}, ctrVoting))) by
(destruct x; destruct x0 ; destruct x1; destruct x2; destruct x3 ; vm_compute; try easy; Simpl).
apply fstep_imp_detstep with (c2:=c') (t2:=t) in F; Simpl. Qed. 

(*If input signals are the same and pure, no glitches, then after voting the output equals to the truplicated output
buses after the TMR-ed FSM of control block*)
Lemma tmrVotRelat:
forall a1 a2 a3  b1 b2 b3 fI t,  pure_bset fI->  pure_bset {t, t, t} ->
step (tmr (ctrBl_dtr a1 a2 a3)) {fI, fI, fI} {t, t, t} (tmr (ctrBl_dtr b1 b2 b3)) 
-> 
step (ctrBlockTMR a1 a2 a3)  {fI, fI, fI} t (ctrBlockTMR b1 b2 b3).
Proof. 
intros.
unfold ctrBlockTMR. eapply Sseq. exact H1.
assert ( exists s, exists c', step ctrVoting {t, t, t} s c' ). apply step_all_ex. Simpl.
Simpl. assert (HA :=  H2). apply votNorm in H2. SimpS. Simpl. Checkpure. 
Qed.