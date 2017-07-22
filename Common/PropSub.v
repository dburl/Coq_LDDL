  
(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        Properties of generic sub-circuits
#</h1>#    
#</center> <hr>#                                           *)
(*          Pascal Fradet - 2014_2015                      *)
(* ------------------------------------------------------- *)

Require Export CirTactics.

Set Implicit Arguments.

(* ####################################################### *)
(** *           Properties of some plugs                   *)

Lemma fact_shuffle : forall A B C D a b c d t cb, 
                    step (shuffle A B C D) {{a, b}, {c, d}} t cb -> t={{a,c},{b,d}} /\ cb=(shuffle A B C D).
Proof. introv H. unfold shuffle in H. Dd_buset t. Invstep H. SimpS. easy. Qed.


Lemma fact1_swap_lr : forall S U a b fA fB a' b' fA' fB', 
                      stepg (SWAP_LR S U (§ # §)) {a, b, {fA, fB}} {a',{fA',fB'}, b'} (SWAP_LR S U (§ # §))
                   -> (b=b' /\ fA=fA' /\ fB=fB')
                   \/ (a=a' /\ fA=fA' /\ fB=fB')
                   \/ (a=a' /\ b=b' /\ fB=fB')
                   \/ (a=a' /\ b=b' /\ fA=fA').
Proof. introv H. unfold SWAP_LR in H. Invstep H; SimpS; easy. Qed.

(* ####################################################### *)
(** *           Properties of voter                        *)

Lemma step1_Voter31 : forall x1 x2 x c, step Voter31 {{x1, x1},x2} x c 
                                   -> (x=x1 /\ c=Voter31).
Proof.
introv H. 
assert (F:fstep Voter31 {x1, x1, x2} = Some (x1,Voter31)).
- Destruct_s x1 as x1; destruct x1; Destruct_s x2 as x2; destruct x2; cbv; easy.  
- eapply fstep_imp_detstep in F; try exact H. destruct F. easy.
Qed.

Lemma step2_Voter31 : forall x1 x2 x c, step Voter31 {{x1, x2},x1} x c 
                                   -> (x=x1 /\ c=Voter31).
Proof.
introv H. 
assert (F:fstep Voter31 {x1, x2, x1} = Some (x1,Voter31)).
- Destruct_s x1 as x1; destruct x1; Destruct_s x2 as x2; destruct x2; cbv; easy.   
- eapply fstep_imp_detstep in F; try exact H. destruct F. easy.
Qed.

Lemma step3_Voter31 : forall x1 x2 x c, step Voter31 {{x2, x1},x1} x c 
                                   -> (x=x1 /\ c=Voter31).
Proof.
introv H. 
assert (F:fstep Voter31 {x2, x1, x1} = Some (x1,Voter31)).
- Destruct_s x1 as x1; destruct x1; Destruct_s x2 as x2; destruct x2; cbv; easy.   
- eapply fstep_imp_detstep in F; try exact H. destruct F. easy.
Qed.

(* ####################################################### *)
(** *              Properties of mux                       *)


Lemma step_mux21 : forall s a b x c, step Mux21 {s, {a, b}} x c 
                              -> (s=(~1) /\ x=b /\ c=Mux21)
                              \/ (s=(~0) /\ x=a /\ c=Mux21)
                              \/ (s=(~?)/\ c= Mux21  /\ (x=(~?) \/ x=(~0))).
Proof.
introv H. Combcode H. apply step_imp_redcomb in H; try (solve [repeat constructor]).
Destruct_s s as s; Destruct_s a as a; Destruct_s b as b.
destruct s; destruct a; destruct b; cbn in H; subst; try easy; try (right; easy).
Qed.


(* ####################################################### *)
(** *           Properties of triplicated voters           *)

Lemma fact1_Tvoter31 : forall (x y:{|§|}) t c, step Tvoter31 {x,y,y} t c -> t={y,y,y} /\ c=Tvoter31.

Proof.
introv H.
assert (F:fstep Tvoter31 {x,y,y} = Some ({y,y,y},Tvoter31))
by (Destruct_s x as x; destruct x; Destruct_s y as y; destruct y; cbv; easy).
eapply fstep_imp_detstep in F; try exact H. destruct F; subst. easy.
Qed.

Lemma fact2_Tvoter31 : forall (x y:{|§|}) t c, step Tvoter31 {y,x,y} t c -> t={y,y,y} /\ c=Tvoter31.

Proof.
introv H.
assert (F:fstep Tvoter31 {y,x,y} = Some ({y,y,y},Tvoter31))
by (Destruct_s x as x; destruct x; Destruct_s y as y; destruct y; cbv; easy).
eapply fstep_imp_detstep in F; try exact H. destruct F; subst. easy.
Qed.

Lemma fact3_Tvoter31 : forall (x y:{|§|}) t c, step Tvoter31 {y,y,x} t c -> t={y,y,y} /\ c=Tvoter31.

Proof.
introv H.
assert (F:fstep Tvoter31 {y,y,x} = Some ({y,y,y},Tvoter31))
by (Destruct_s x as x; destruct x; Destruct_s y as y; destruct y; cbv; easy).
eapply fstep_imp_detstep in F; try exact H. destruct F; subst. easy.
Qed.
