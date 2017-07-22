(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-   Inversion lemmas

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)
(*
Add LoadPath "..\..\Common\".
Require Import CirReflect . 
Add LoadPath "..\..\TMRProof\".
Require Import tmrDef.
Add LoadPath "..\". *)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import tmrDef.
Require Import dtrTransform relationPred relationProp. 

Set Implicit Arguments.

(** Inversion theorems for stepg of DTR memory block - EVEN clock cycle*)

(*State predicates for memory block during odd clock cycles*)

(*Memory block state- no errors inside*)
Definition mbg1 S T s t (sO rO fO f :{|§|}) b'' b' b c1 (c2': circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)))
:=
(exists (lhsPar' : circuit (((§ # §) # §) # (§ # §)) ((§ # ((§ # §) # §)) # (§ # §))) 
  (dNB rNB:bool) (c1' : circuit ((S # §) # ((§ # §) # §)) ((T # §) # ((§ # §) # §)))
  ( so1 s1 r1 f1 rO1 s2 si1 s3 r3 f3  dN rN :{|§|}), (bset2bool rN rNB /\
   bset2bool dN dNB /\  
step rhsPar {si1, {s3, r3, f3 , {rO1, s2}}} {sO, rO, fO ,dN, rN} rhsPar) /\
step c1 {s, so1, {s1, r1, f1}} {t, si1, {s3, r3, f3}} c1' /\
step (lhsPar b b') {~ 1, ~ 0, f, {bool2bset b'', bool2bset b'}} {so1, {s1, r1, f1}, {rO1, s2}} lhsPar'
/\ c2'=mbcore dNB rNB lhsPar' c1' rhsPar).

(*Memory block state- lhsPar is corrupted inside*)
Definition mbg12  S T s t (sO rO fO f:{|§|}) b'' b' b c1 (c2': circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)))
:=
(exists (lhsPar' : circuit (((§ # §) # §) # (§ # §)) ((§ # ((§ # §) # §)) # (§ # §))) 
  (dNB rNB:bool) (c1' : circuit ((S # §) # ((§ # §) # §)) ((T # §) # ((§ # §) # §)))
  ( so1 s1 r1 f1 rO1 s2 si1 s3 r3 f3  dN rN :{|§|}), (bset2bool rN rNB /\ bset2bool dN dNB /\
step rhsPar {si1, {s3, r3, f3 , {rO1, s2}}} {sO, rO, fO ,dN, rN} rhsPar) /\
step c1 {s, so1, {s1, r1, f1}} {t, si1, {s3, r3, f3}} c1' /\
stepg (lhsPar b b') {~ 1, ~ 0, f, {bool2bset b'', bool2bset b'}} {so1, {s1, r1, f1}, {rO1, s2}} lhsPar'
/\ c2'=mbcore dNB rNB lhsPar' c1' rhsPar).

(*Memory block state- internal unknown circuit c1 is corrupted*)
Definition mbg13 S T s t (sO rO fO f:{|§|}) b'' b' b c1 (c2': circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)))
:=
(exists (lhsPar' : circuit (((§ # §) # §) # (§ # §)) ((§ # ((§ # §) # §)) # (§ # §))) 
  (dNB rNB:bool) (c1' : circuit ((S # §) # ((§ # §) # §)) ((T # §) # ((§ # §) # §)))
  ( so1 s1 r1 f1 rO1 s2 si1 s3 r3 f3  dN rN :{|§|}), (bset2bool rN rNB /\ bset2bool dN dNB /\
step rhsPar {si1, {s3, r3, f3 , {rO1, s2}}} {sO, rO, fO  ,dN, rN} rhsPar) /\
stepg c1 {s, so1, {s1, r1, f1}} {t, si1, {s3, r3, f3}} c1' /\
step (lhsPar b b') {~ 1, ~ 0,  f, {bool2bset b'', bool2bset b'}} {so1, {s1, r1, f1}, {rO1, s2}} lhsPar'
/\ c2'=mbcore dNB rNB lhsPar' c1' rhsPar).

(*Memory block state- rhsPar is corrupted*)
Definition mbg16 S T s t (sO rO fO f:{|§|}) b'' b' b c1 (c2': circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)))
:=
(exists (lhsPar' : circuit (((§ # §) # §) # (§ # §)) ((§ # ((§ # §) # §)) # (§ # §))) 
  (dNB rNB:bool) (c1' : circuit ((S # §) # ((§ # §) # §)) ((T # §) # ((§ # §) # §)))
  ( so1 s1 r1 f1 rO1 s2 si1 s3 r3 f3  dN rN :{|§|}), (bset2bool rN rNB /\ bset2bool dN dNB /\
stepg rhsPar {si1, {s3, r3, f3 , {rO1, s2}}} {sO, rO, fO ,dN, rN} rhsPar) /\
step c1 {s, so1, {s1, r1, f1}} {t, si1, {s3, r3, f3}} c1' /\
step (lhsPar b b') {~ 1, ~ 0, f, {bool2bset b'', bool2bset b'}} {so1, {s1, r1, f1}, {rO1, s2}} lhsPar'
/\ c2'=mbcore dNB rNB lhsPar' c1' rhsPar).

(*Memory block state- one output from a memory cell is corrupted*)
Definition mbg17  S T s t (sO rO fO f:{|§|}) b'' b' b c1 (c2': circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)))
:=
(exists (lhsPar' : circuit (((§ # §) # §) # (§ # §)) ((§ # ((§ # §) # §)) # (§ # §))) 
  (dNB rNB:bool) (c1' : circuit ((S # §) # ((§ # §) # §)) ((T # §) # ((§ # §) # §)))
  ( so1 s1 r1 f1 rO1 s2 si1 s3 r3 f3  dN rN gl :{|§|}), (bset2bool rN rNB /\bset2bool dN dNB /\
   introglitch (bool2bset b') gl /\ 
step rhsPar {si1, {s3, r3, f3 , {rO1, s2}}} {sO, rO, fO ,dN, rN} rhsPar) /\
step c1 {s, so1, {s1, r1, f1}} {t, si1, {s3, r3, f3}} c1' /\
step (lhsPar b b') {~ 1, ~ 0, f, {bool2bset b'', gl}} {so1, {s1, r1, f1}, {rO1, s2}} lhsPar'
/\ c2'=mbcore dNB rNB lhsPar' c1' rhsPar).

(*Memory block state- one output from another memory cell is corrupted*)
Definition mbg18  S T s t (sO rO fO f :{|§|}) b'' b' b c1 (c2': circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)))
:=
(exists (lhsPar' : circuit (((§ # §) # §) # (§ # §)) ((§ # ((§ # §) # §)) # (§ # §))) 
  (dNB rNB:bool) (c1' : circuit ((S # §) # ((§ # §) # §)) ((T # §) # ((§ # §) # §)))
  ( so1 s1 r1 f1 rO1 s2 si1 s3 r3 f3  dN rN gl :{|§|}), (bset2bool rN rNB /\ bset2bool dN dNB /\
   introglitch (bool2bset b'') gl /\ 
step rhsPar {si1, {s3, r3, f3 , {rO1, s2}}} {sO, rO, fO , dN, rN} rhsPar) /\
step c1 {s, so1, {s1, r1, f1}} {t, si1, {s3, r3, f3}} c1' /\
step (lhsPar b b') {~ 1, ~ 0, f, {gl, bool2bset b'}} {so1, {s1, r1, f1}, {rO1, s2}} lhsPar'
/\ c2'=mbcore dNB rNB lhsPar' c1' rhsPar).

(*Disjunction of all possible corruption cases for even cycles*)
Definition mbgG  S T s t (sO rO fO f:{|§|}) b'' b' b c1 (c2': circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)))
:= mbg12   s t sO rO fO f b'' b' b c1 c2'
\/ mbg13   s t sO rO fO f b'' b' b c1 c2'
\/ mbg16   s t sO rO fO f b'' b' b c1 c2'
\/ mbg17   s t sO rO fO f b'' b' b c1 c2'
\/ mbg18   s t sO rO fO f b'' b' b c1 c2'.

(*Inverstion of the loop constructor in memory block transformation*)
Lemma invstepgDTRloop1 : forall S T (s:{|S|}) (t:{|T|}) (sO rO fO f :{|§|}) (b'' b' b:bool)
                                (c1 : circuit ((S # §) # ((§ # §) # §)) ((T # §) # ((§ # §) # §)) )
                                (c2': circuit (S # ((§ # §) # §)) (T # ((§ # §) # §))), 
                          pure_bset s-> pure_bset f
                       -> stepg (memBlock b'' b' b' b c1) {s, {~ 1, ~ 0, f}} {t, {sO, rO, fO}}  c2'
                       -> mbgG s t sO rO fO f b'' b' b c1 c2'.
Proof. 
introv P1 P2 H0.  unfold memBlock in H0. unfold lhsMB in H0. unfold rhsMB in H0.
Invstep H0; SimpS.
 - unfold mbgG. left. unfold mbg12. 
   exists  x66 x60 x61 x62 x0 x3. exists x5 x4 x1 x2 x54 x51. exists x52 x50 x32 x31. 
   dupl H9 Hcopy. apply step_comb_cir in H9. Inverts H9.
   repeat split; try easy. repeat constructor.
 - unfold mbgG. right. left. unfold mbg13.
   exists  x62 x60 x61 x64 x42 x44. exists x45 x43 x40 x41 x5 x1. exists x3 x2 x11 x10. 
   dupl H16 Hcopy. apply step_comb_cir in H16. Inverts H16.
   repeat split; try easy. repeat constructor.
 - unfold mbgG. right. right. left. unfold mbg16.
   exists  x61 x59 x60 x62 x41 x43. exists x44 x42 x39 x40 x32 x30. exists x31 x29 x2 x0. 
   dupl H15 Hcopy. apply stepg_comb_cir in H15. Inverts H15.
   repeat split; try easy. repeat constructor.
 - unfold mbgG. right. right. right. left. unfold mbg17.
   exists x86 x66 x69 x31 x9 x11. exists x12 x10 x7 x8 x57 x54. exists x55 x53 x33 x32 x68. 
   dupl H14 Hcopy. apply step_comb_cir in H14. Inverts H14.
   repeat split; try easy. repeat constructor.
 - unfold mbgG. right. right. right. right. unfold mbg18.
   exists  x86 x67 x69 x31 x9 x11. exists x12 x10 x7 x8 x57 x54. exists x55 x53 x33 x32 x66. 
   dupl H14 Hcopy. apply step_comb_cir in H14. Inverts H14.
   repeat split; try easy. repeat constructor.
Qed.

