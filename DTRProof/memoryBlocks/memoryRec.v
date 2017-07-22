(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-   states transitions during recovery for memoty block

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)
(*
Add LoadPath "..\..\Common\".
Require Import CirReflect . 
Add LoadPath "..\..\TMRProof\".
Require Import tmrDef.
Add LoadPath "..\".*)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import dtrTransform relationPred leftStep leftStepg rightStep.

Set Implicit Arguments.

(* ##################################################################### *)
(** Properties of Memory Block during the recovery process               *)
(* ##################################################################### *)

Lemma stepr4_mb_d'rr' : forall S T (c c' c'':circuit S T) cc cc' t2 s t f, 
                       pure_bset s -> dtrec_d'rr' c c' cc 
                    -> step c' s t c''
                    -> step cc {s,{~0,~1,bool2bset f}} t2 cc'
                    -> (exists e,t2 = {t,{~0,~1,bool2bset e}}) /\ dtrec_rr' c' c'' cc'.
Proof. 
intros S T c. induction c.
- introv P1 R H HT. Inverts R. Invstep HT. Simpl. Inverts H1. split; Simpl.
  constructor.
- introv P1 R H HT. Inverts R. Invstep HT. Simpl. Inverts H1. split; Simpl.  
  constructor.
- introv P1 R H HT. Inverts R. Inverts H. Inverts HT. Simpl.
  apply IHc1 with (c':=c1') (c'':=c1'0) (t:=t0) in H3; Simpl. 
  apply IHc2 with (c':=c2') (c'':=c2'0)  (t:=t) in H12; Simpl.
  split; Simpl. constructor; Simpl.
- introv P1 R H HT. Inverts R. unfold  SWAP_LR in HT. unfold  SWAP_LS in HT.
  Invstep HT. SimpS. 
  apply IHc1 with (c':=c1') (c'':=x25) (t:=x) in H0; Simpl.
  apply IHc2 with (c':=c2') (c'':=x33) (t:=x0) in H11; Simpl.
  split; Simpl. constructor; easy.
- introv P1 R H HT. Inverts R. unfold memBlock in HT. unfold lhsMB in HT. 
  unfold rhsMB in HT. Inverts H7. Invstep HT. SimpS.
  apply step_rhs in H15. SimpS. rename x87 into b''.
  apply step_lhs with (fai:= f) (sav:=false) 
                            (rol:= true) (d:= d) (r:= r) in H18; try easy.
  destruct H18. SimpS. simpl in H1.
  rewrite eqb_reflx in H2. unfold bool2bset in H2. simpl in H2.
  apply IHc with (c':=c'0) (c'':=x3) (t:={t, x71}) in H2; try easy; Checkpure;
  destruct H2; Simpl. simpl. constructor.
Qed.
  
Lemma stepr3_mb_d'rr' : forall S T (c c' c'':circuit S T) cc cc' t2 s t f, 
                       pure_bset s -> dtrec_d'rr' c c' cc 
                    -> step c' s t c''
                    -> step cc {s,{~0,~1,bool2bset f}} t2 cc'
                    -> (exists e,t2 = {t,{~0,~1,bool2bset e}}) /\ dtrec_d'rr' c' c'' cc'.
Proof. 
intros S T c. induction c.
- introv P1 R H HT. Inverts R. Invstep HT. Simpl. Inverts H1. split; Simpl.
  constructor.
- introv P1 R H HT. Inverts R. Invstep HT. Simpl. Inverts H1. split; Simpl.  
  constructor.
- introv P1 R H HT. Inverts R. Inverts H. Inverts HT. Simpl.
  apply IHc1 with (c':=c1') (c'':=c1'0) (t:=t0) in H3; Simpl. 
  apply IHc2 with (c':=c2') (c'':=c2'0)  (t:=t) in H12; Simpl.
  split; Simpl. constructor; Simpl.
- introv P1 R H HT. Inverts R. unfold  SWAP_LR in HT. unfold  SWAP_LS in HT.
  Invstep HT. SimpS. 
  apply IHc1 with (c':=c1') (c'':=x25) (t:=x) in H0; Simpl.
  apply IHc2 with (c':=c2') (c'':=x33) (t:=x0) in H11; Simpl.
  split; Simpl. constructor; easy.
- introv P1 R H HT. Inverts R. unfold memBlock in HT. unfold lhsMB in HT. 
  unfold rhsMB in HT. Inverts H7. Invstep HT. SimpS.
  apply step_rhs in H15. SimpS. rename x87 into b''.
  apply step_lhs with (fai:= f) (sav:=false) 
                            (rol:= true) (d:= d) (r:= r) in H18; try easy.
  destruct H18. SimpS. simpl in H1.
  rewrite eqb_reflx in H2. unfold bool2bset in H2. simpl in H2.
  apply IHc with (c':=c'0) (c'':=x3) (t:={t, x71}) in H2; try easy; Checkpure;
  destruct H2; Simpl. simpl. constructor.
Qed.

Lemma stepr5_mb_rr' :  forall S T (c c':circuit S T) cc cc' t2 s t f,
                       pure_bset s -> dtrec_rr' c c' cc 
                    -> step c s t c'
                    -> step cc {s,{~1,~0,bool2bset f}} t2 cc'
                    -> (exists e, t2 = {t,{~1,~0,bool2bset e}}) /\ dtr0_r' c c' cc'.
Proof.
intros S T c. induction c.
- introv P1 R H HT. Inverts R. Invstep HT. Simpl. Inverts H1. split; Simpl.
  constructor.
- introv P1 R H HT. Inverts R. Invstep HT. Simpl. Inverts H1. split; Simpl.  
  constructor.
- introv P1 R H HT. Inverts R. Inverts H. Inverts HT. Simpl.
  apply IHc1 with (c':=c1') (t:=t0) in H3; Simpl. 
  apply IHc2 with (c':=c2')  (t:=t) in H11; Simpl.
  split; Simpl. constructor; Simpl.
- introv P1 R H HT. Inverts R. unfold  SWAP_LR in HT. unfold  SWAP_LS in HT.
  Invstep HT. Inverts H13. SimpS. 
  apply IHc1 with (cc':= x18) (cc:=c21) (t2:={x5, {x11, x12, x10}}) (s:=x1) (t:=x) (f:=f) in H2; Simpl.
  apply IHc2 with (cc':=x35) (c':=x33) (t2:={x8, {x16, x17, x15}}) (s:=x2) (t:=x0) (f:=x3) in H11; Simpl.
  split; Simpl. constructor; easy.
- introv P1 R H HT. Inverts R. unfold memBlock in HT. unfold lhsMB in HT. 
  unfold rhsMB in HT. Inverts H7. Invstep HT. SimpS. Inverts H20.
  apply step_rhs in H15. SimpS. rename x87 into b''.
  apply step_lhs with (fai:= f) (sav:=true) 
                            (rol:= false) (d:= b'') (r:= r) in H18; try easy.
  destruct H18. SimpS. simpl in H1.
  rewrite eqb_reflx in H2. unfold bool2bset in H2. simpl in H2.
  apply IHc with (c':=x3) (t:={t, x71})  in H2; try easy; try Checkpure;
  destruct H2; SimpS.
    + exists x; easy.
    + Simpl.
    + simpl. Simpl. constructor.
Qed.

Lemma stepr2_mb_d'rr' : forall S T (c' c'':circuit S T) cc cc' t2 s t, 
                      pure_bset s -> dtrec_d'rr' c'' c' cc 
                   -> step c' s t c''
                   -> step cc {s,{~0,~1,~1}} t2 cc'
                   -> t2 = {t,{~0,~1,~1}} /\ dtrec_d'rr' c' c'' cc'.
Proof. 
introv P R H HT. induction H.
- Inverts R; split; Invstep HT; Simpl. constructor.
- Inverts R; split; Invstep HT; Simpl. constructor.
- Inverts R. Inverts HT.
  Apply IHstep1 in H6;  Simpl.
  Apply IHstep2 in H12; Simpl. split; constructor; easy.
- Inverts R. unfold SWAP_LS in HT. unfold SWAP_LR in HT.
  Invstep HT. SimpS.
  Apply IHstep1 in H0; Simpl.
  Apply IHstep2 in H11; Simpl.
  split; Simpl. constructor; easy.
- Inverts R. unfold memBlock in HT. 
  unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS. Inverts H9.
  apply step_rhs in H17. 
  apply step_lhs with (fai:=true) (rol:=true) 
                            (sav:=false) (d:= d) (r:= r) in H20; Simpl.
  assert (HE: (negb (eqb d' d) || true) = true)by(destruct d'; destruct d; easy).
  rewrite HE in H2. unfold bool2bset in H2. simpl in H2.
  Apply IHstep in H2; Simpl. split; Simpl.
  repeat constructor. Simpl.
Qed.