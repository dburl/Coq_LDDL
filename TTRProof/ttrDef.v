(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The triple modular redundancy transformation   
#</h1>#    
-  Relation predicates between states of source and transformed circuits
-  Definitions of the basic constituents  (protected control block, memory block)
-  Definition of the ttr transformation

P              Pascal Fradet - Inria - 2014  
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\Common\".
Require Export CirReflect. 

Set Implicit Arguments.

(* ####################################################### *)
(** *         Circuits used in TTR transformation          *)
(* ####################################################### *)

(** Control block for TTR transformation, takes the circuit input,    *)
(** transmits it unchanged along with the fetchA and fetch B signals  *)
(** cb_ttr s = [s,[fetchA,fetchB]]                                    *)  
(*  The control block is protected (triplication + voters)            *)
(* it is expressed so that a large sub-circuit can be analyzed by     *)
(* reflection (i.e. all input types are known)                        *)

Definition Celb (b:bool): circuit § § := -{b}-SWAP. 

Definition cb_ttrb (b1 b2 b3 b4 b5:bool): circuit § ((§ # §) # §)
           := -{b1}--{b2}-(FORK-o--|Tvoter31-o--|-|Celb b3,Celb b4|-,Celb b5|-,ID|-
                                 -o-(shuffle (§#§) § (§#§) §)-o--|(shuffle § § § §) 
                                 -o--|OR-o-NOT,OR-o-NOT|-,OR-o-NOT|-
                                 -o-Tvoter31 -o--|FORK-o-RSH,ID|-).

(* The three states of the control block  *)
Definition cb_ttr S : circuit S (S#(§#§))
           :=  -{false}--|ID,cb_ttrb false false false false false|--o-RSH.
Definition cb_ttr1 S : circuit S (S#(§#§))
           :=  -{true}--|ID,cb_ttrb true true false false false|--o-RSH.
Definition cb_ttr2 S : circuit S (S#(§#§))
           :=  -{false}--|ID,cb_ttrb false false true true true|--o-RSH.

(* Corrupted control block predicate (only one cell corrupted)  *)
Inductive ccb : bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Prop := 
| Iccb_1 : forall b1 b2 z, ccb b1 b2 z  b1 b1 b2 b2 b2
| Iccb_2 : forall b1 b2 z, ccb b1 b2 b1 z  b1 b2 b2 b2
| Iccb_3 : forall b1 b2 z, ccb b1 b2 b1 b1 z  b2 b2 b2
| Iccb_4 : forall b1 b2 z, ccb b1 b2 b1 b1 b1 z  b2 b2
| Iccb_5 : forall b1 b2 z, ccb b1 b2 b1 b1 b1 b2 z  b2
| Iccb_6 : forall b1 b2 z, ccb b1 b2 b1 b1 b1 b2 b2 z.
Hint Constructors ccb.

(** ** Memory block for TTR transformation  *)


(**      Delay line (last two cells)        *)

Definition dl_ttr (b b':bool) : circuit § (§#(§#§)) 
           := FORK -o--|ID,(-{b}-SWAP) -o- FORK -o--|ID,(-{b'}-SWAP)|-|-.

(** The main plug for voting (re-wiring only) *)

Definition Plug1TTR : circuit ((((§#(§#§))#(§#§))#§)#§) ((§#(§#§))#(§#(§#§))#§) 
:= LSH -o- SWAP -o- RSH -o- SWAP -o- -|ID, -|ID,(SWAP_RL § § §)-o- RSH|- -o-RSH
       -o- -|(shuffle § § § §), ID|- |- -o- RSH -o- -|(shuffle § § (§#§) (§#§)),ID|-.

(** Voting component (2 muxes + 2 voters + 2 cells) of the TTR memory block *)
(** (i1,i2,i3), fetchA,fetchB -> so  *)

Definition voting_ttr kA kB : circuit ((§#(§#§))#(§#§)) § 
           := Cloop kA (Cloop kB (Plug1TTR -o--|-|Mux21,Mux21|-, ID|--o-FORK 
                                            -o--|Voter31 -o- FORK,Voter31|-)).

(** The memory block  (combining delay line and voting) *)

Definition mb_ttr (b2 b3 kA kB:bool) : circuit (§#(§#§)) (§#(§#§))
           := (DUPL § (§#§))-o--|-|dl_ttr b2 b3,ID|--o-(voting_ttr kA kB),ID|-.


(* ####################################################### *)
(** *   The Triple Time Redundancy transformation          *)
(*                     DSN version                         *)
(* ####################################################### *)

Fixpoint ttr S T (c: circuit S T): circuit (S#(§#§)) (T#(§#§)) :=
match c with
| Cgate g             => -|Cgate g, ID|- 
| Cplug p             => -|Cplug p, ID|-
| Cseq c1 c2          => (ttr c1) -o- (ttr c2)
| @Cpar s t u v c1 c2 => (SWAP_LR s u (§#§))-o--|ttr c1,ID|--o-(SWAP_LS t (§#§)u)-o--|ID,ttr c2|--o-RSH 
| @Cloop s t b c      => -{b}-((SWAP_LS s (§#§) §) -o- -|ID ,mb_ttr b b b b|- -o- RSH
                                 -o- (ttr c) -o- (SWAP_LR t § (§#§))) 
end.

(** The global transformation plugging the control block *)

Definition TTR S T (c: circuit S T): circuit S (T#(§#§)) :=  (cb_ttr S) -o- (ttr c).

(** Type of predicates on memory block *)

Definition Pmb_type := bool -> bool -> bool -> bool -> bool -> bool -> bool -> Prop.

(* Definition of the different states of circuits upon normal execution  *)
(* There are 3 different states corresponding to execution cycles        *)
(*  3i-2, 3i-1 and 3i . The predicates smb0, smb1 and smb2               *)
(* characterize the states of memory blocks at these steps               *)
(* ttrs c c' c3 relates the state of the transformed circuit c3          *)
(* according to the states of the original circuit before (c)            *)
(* and after (c') a reduction step.                                      *)


Section Def_ttrs.

Variable smb : Pmb_type.

Inductive ttrs: forall S T, circuit S T -> circuit S T -> circuit (S#(§#§)) (T#(§#§)) -> Prop :=
| TsGate : forall S T (g:gate S T), 
           ttrs (Cgate g) (Cgate g) (-|Cgate g, ID|-)

| TsPlug : forall S T (p:plug S T), 
           ttrs (Cplug p) (Cplug p) (-|Cplug p, ID|-)

| TsSeq  : forall S T U (c1 c'1:circuit S T) (c2 c'2:circuit T U) c31 c32, 
           ttrs c1 c'1 c31 -> ttrs c2 c'2 c32 
        -> ttrs (c1-o-c2) (c'1-o-c'2) (c31-o-c32)

| TsPar  : forall S T U V (c1 c'1:circuit S T) (c2 c'2:circuit U V) c31 c32, 
           ttrs c1 c'1 c31 -> ttrs c2 c'2 c32 
        -> ttrs (-|c1,c2|-) (-|c'1,c'2|-)  
                            ((SWAP_LR S U (§#§))-o--|c31,ID|--o-(SWAP_LS T (§#§) U)-o--|ID,c32|--o-RSH )

| TsLoop : forall S T (c c':circuit (S#§) (T#§)) c3 b b' d1 d2 d3 kA kB,
           ttrs c c' c3 -> smb b b' d1 d2 d3 kA kB
        -> ttrs (-{b}-c) (-{b'}-c') (-{d1}-((SWAP_LS S (§#§) §) -o- -|ID ,mb_ttr d2 d3 kA kB|- -o- RSH
                                 -o- c3 -o- (SWAP_LR T § (§#§)))).
End Def_ttrs.
Hint Constructors ttrs.

(* The predicates relating the state of source and transformed circuits *)
(* after 3i-2, 3i-1, 3i reduction steps                                 *)

Inductive smb0 (b b':bool): bool -> bool -> bool -> bool -> bool -> Prop := 
| Ismb0 : smb0 b b' b' b' b' b b.

Inductive smb1 (b b':bool): bool -> bool -> bool -> bool -> bool -> Prop := 
| Ismb1 : smb1 b b' b' b b b b.

Inductive smb2 (b b':bool): bool -> bool -> bool -> bool -> bool -> Prop := 
| Ismb2 : smb2 b b' b' b' b b b.
Definition ttrs0 := ttrs smb0.
Definition ttrs1 := ttrs smb1.
Definition ttrs2 := ttrs smb2.
Hint Unfold ttrs0 ttrs1 ttrs2.

Lemma ttr_equiv_ttrs0 : forall S T (c:circuit S T) c3,  ttr c = c3 <-> ttrs0 c c c3.
Proof.
split; introv H. 
- induction c; rewrite <- H; try easy.
  + constructor.
    * apply IHc1. easy. 
    * apply IHc2. easy.
  + constructor.
    * apply IHc1. easy.
    * apply IHc2. easy.
  + repeat constructor. apply IHc. easy.
- unfold ttrs0 in H. induction c; Inverts H; try easy.
  + apply IHc1 in H4. apply IHc2 in H9. subst. easy.
  + apply IHc1 in H3. apply IHc2 in H10. subst. easy.
  + apply IHc in H5. Inverts H8. subst. easy.
Qed.

(** ** Specification of possible corrupted states                  *)
(* Different cases of corruption of memory blocks                  *)

(* cmbx_y : characterizes a memory block at step x (ie, 3x-2)      *)
(*          corrupted at cell y                                    *)
Inductive cmb0 : nat ->  Pmb_type := 
| Icmb0_1 : forall b b' z, cmb0 1 b b' z  b' b' b b
| Icmb0_2 : forall b b' z, cmb0 2 b b' b' z  b' b b
| Icmb0_3 : forall b b' z, cmb0 3 b b' b' b' z  b b
| Icmb0_4 : forall b b' z, cmb0 4 b b' b' b' b' z b
| Icmb0_5 : forall b b' z, cmb0 5 b b' b' b' b' b z.

Inductive cmb1 : nat ->  Pmb_type := 
| Icmb1_1 : forall b b' z, cmb1 1 b b' z  b b b b
| Icmb1_2 : forall b b' z, cmb1 2 b b' b' z b b b
| Icmb1_3 : forall b b' z, cmb1 3 b b' b' b z b b
| Icmb1_4 : forall b b' z, cmb1 4 b b' b' b b z b
| Icmb1_5 : forall b b' z, cmb1 5 b b' b' b b b z.

Inductive cmb2 : nat ->  Pmb_type := 
| Icmb2_1 : forall b b' z, cmb2 1 b b' z  b' b b b
| Icmb2_2 : forall b b' z, cmb2 2 b b' b' z  b b b
| Icmb2_3 : forall b b' z, cmb2 3 b b' b' b' z b b
| Icmb2_4 : forall b b' z, cmb2 4 b b' b' b' b z b
| Icmb2_5 : forall b b' z, cmb2 5 b b' b' b' b b z.


(* Corruption of memory blocks at the three differents cycles *)

Section Def_ttrg.

Variable cmb : Pmb_type.

Inductive ttrg: forall S T, circuit S T -> circuit S T -> circuit (S#(§#§)) (T#(§#§))-> Prop :=
| TgGate : forall S T (g:gate S T), 
            ttrg (Cgate g) (Cgate g) (-|Cgate g, ID|-)

| TgPlug : forall S T (p:plug S T), 
           ttrg (Cplug p) (Cplug p) (-|Cplug p, ID|-)

| TgSeq  : forall S T U (c1 c1':circuit S T) (c2 c2':circuit T U) c31 c32, 
           ttrg c1 c1' c31 -> ttrg c2 c2' c32 -> ttrg (c1-o-c2) (c1'-o-c2') (c31-o-c32) 

| TgPar  : forall S T U V (c1 c1':circuit S T) (c2 c2':circuit U V) c31 c32, 
           ttrg c1 c1' c31 -> ttrg c2 c2' c32 
        -> ttrg (-|c1,c2|-) (-|c1',c2'|-) ((SWAP_LR S U (§#§))-o--|c31,ID|--o-(SWAP_LS T (§#§) U)-o--|ID,c32|--o-RSH )

| TgLoop : forall S T (c c':circuit (S#§) (T#§)) c3 b b' d1 d2 d3 kA kB,
           ttrg c c' c3 -> cmb b b' d1 d2 d3 kA kB
        -> ttrg (-{b}-c) (-{b'}-c') (-{d1}-((SWAP_LS S (§#§) §) -o- -|ID ,mb_ttr d2 d3 kA kB|- -o- RSH
                                    -o- c3 -o- (SWAP_LR T § (§#§)))).
End Def_ttrg.
Hint Constructors ttrg.

Inductive cmb0_d1kA :Pmb_type := 
| Icmb0d1KA : forall b b' y z, cmb0_d1kA b b' y  b' b' z b.

Inductive cmb1_d1kA :Pmb_type := 
| Icmb1d1KA : forall b b' y z, cmb1_d1kA b b' y  b b z b.

Inductive cmb2_d1kA :Pmb_type := 
| Icmb2d1KA : forall b b' y z, cmb2_d1kA b b' y  b' b z b.


Definition ttrg0_d1 := ttrg (cmb0 1).
Definition ttrg0_d2 := ttrg (cmb0 2).
Definition ttrg0_d3 := ttrg (cmb0 3).
Definition ttrg0_kA := ttrg (cmb0 4).
Definition ttrg0_kB := ttrg (cmb0 5).
Definition ttrg0_d1kA   := ttrg (cmb0_d1kA).
Definition ttrg0_d2d3kB S T (c c':circuit S T) c3 := ttrg0_d2 c c' c3 \/ ttrg0_d3 c c' c3
                                                  \/ ttrg0_kB c c' c3.
(*
Definition ttrg0 S T (c c':circuit S T) c3 := ttrg0_d1 c c' c3 \/ ttrg0_d2 c c' c3 \/ ttrg0_d3 c c' c3
                                           \/ ttrg0_kA c c' c3 \/ ttrg0_kB c c' c3. *)

Definition ttrg1_d1 := ttrg (cmb1 1).
Definition ttrg1_d2 := ttrg (cmb1 2).
Definition ttrg1_d3 := ttrg (cmb1 3).
Definition ttrg1_kA := ttrg (cmb1 4).
Definition ttrg1_kB := ttrg (cmb1 5).
Definition ttrg1_d1kA   := ttrg (cmb1_d1kA).
Definition ttrg1_d2d3kB S T (c c':circuit S T) c3 := ttrg1_d2 c c' c3 \/ ttrg1_d3 c c' c3
                                                  \/ ttrg1_kB c c' c3.
(* Definition ttrg1 S T (c c':circuit S T) c3 := ttrg1_d1 c c' c3 \/ ttrg1_d2 c c' c3 \/ ttrg1_d3 c c' c3
                                           \/ ttrg1_kA c c' c3 \/ ttrg1_kB c c' c3. *)
Definition ttrg2_d1 := ttrg (cmb2 1).
Definition ttrg2_d2 := ttrg (cmb2 2).
Definition ttrg2_d3 := ttrg (cmb2 3).
Definition ttrg2_kA := ttrg (cmb2 4).
Definition ttrg2_kB := ttrg (cmb2 5).
Definition ttrg2_d1kA   := ttrg (cmb2_d1kA).
Definition ttrg2_d2d3kB S T (c c':circuit S T) c3 := ttrg2_d2 c c' c3 \/ ttrg2_d3 c c' c3
                                                  \/ ttrg2_kB c c' c3.
(*Definition ttrg2 S T (c c':circuit S T) c3 := ttrg2_d1 c c' c3 \/ ttrg2_d2 c c' c3 \/ ttrg2_d3 c c' c3
                                           \/ ttrg2_kA c c' c3 \/ ttrg2_kB c c' c3.
*)

Hint Unfold ttrg0_d1 ttrg0_d2 ttrg0_d3 ttrg0_kA ttrg0_kB
            ttrg1_d1 ttrg1_d2 ttrg1_d3 ttrg1_kA ttrg1_kB
            ttrg2_d1 ttrg2_d2 ttrg2_d3 ttrg2_kA ttrg2_kB.


(* Being in a correct state implies being in the corresponding (possibly) corrupted state *)


Lemma ttrs1_imp_ttrg1_d2 : forall S T (c c':circuit S T) c3, 
                           ttrs1 c c' c3 -> ttrg1_d2 c c' c3.
Proof.
introv H. induction H; try (constructor; easy).
Inverts H0. constructor. easy. constructor. 
Qed.
Lemma ttrs1_imp_ttrg1_d3 : forall S T (c c':circuit S T) c3, 
                           ttrs1 c c' c3 -> ttrg1_d3 c c' c3.
Proof.
introv H. induction H; try (constructor; easy).
Inverts H0. constructor. easy. constructor. 
Qed.

Lemma ttrs1_imp_ttrg1_kB : forall S T (c c':circuit S T) c3, 
                           ttrs1 c c' c3 -> ttrg1_kB c c' c3.
Proof.
introv H. induction H; try (constructor; easy).
Inverts H0. constructor. easy. constructor. 
Qed.

Lemma ttrs2_imp_ttrg2_d2 : forall S T (c c':circuit S T) c3, 
                           ttrs2 c c' c3 -> ttrg2_d2 c c' c3.
Proof.
introv H. induction H; try (constructor; easy).
Inverts H0. constructor. easy. constructor. 
Qed.
Lemma ttrs2_imp_ttrg2_d3 : forall S T (c c':circuit S T) c3, 
                           ttrs2 c c' c3 -> ttrg2_d3 c c' c3.
Proof.
introv H. induction H; try (constructor; easy).
Inverts H0. constructor. easy. constructor. 
Qed.

Lemma ttrs2_imp_ttrg2_kB : forall S T (c c':circuit S T) c3, 
                           ttrs2 c c' c3 -> ttrg2_kB c c' c3.
Proof.
introv H. induction H; try (constructor; easy).
Inverts H0. constructor. easy. constructor. 
Qed.


Lemma ttrs0_imp_ttrg0_d2 : forall S T (c c':circuit S T) c3, 
                           ttrs0 c c' c3 -> ttrg0_d2 c c' c3.
Proof.
introv H. induction H; try (constructor; easy).
Inverts H0. constructor. easy. constructor. 
Qed.
Lemma ttrs0_imp_ttrg0_d3 : forall S T (c c':circuit S T) c3, 
                           ttrs0 c c' c3 -> ttrg0_d3 c c' c3.
Proof.
introv H. induction H; try (constructor; easy).
Inverts H0. constructor. easy. constructor. 
Qed.

Lemma ttrs0_imp_ttrg0_kB : forall S T (c c':circuit S T) c3, 
                           ttrs0 c c' c3 -> ttrg0_kB c c' c3.
Proof.
introv H. induction H; try (constructor; easy).
Inverts H0. constructor. easy. constructor. 
Qed.

