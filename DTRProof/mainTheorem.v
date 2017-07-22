(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation
#</h1>#
- Main correctness theorem

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\Common\".
Add LoadPath "..\TMRProof\".
Add LoadPath "Transf\".
Add LoadPath "inputBuffers\".
Add LoadPath "outputBuffers\".
Add LoadPath "memoryBlocks\".
Add LoadPath "controlBlock\".
Add LoadPath "globalCircuit\".

Require Import dtrTransform relationPred.
Require Import inputLib controlLib globalLib outputLib memoryLib.

Set Implicit Arguments.

(* ------------------------------------------------------------------------------------- *)
(**             Duplicating streams  (used to model the primary input stream)            *)

CoFixpoint doublStream S (Pis: Stream {|S|}) : Stream {|S|}:=
match Pis with
Cons Pi Pis => Cons Pi (Cons Pi (doublStream Pis))
end.

(* ------------------------------------------------------------------------------------- *)
(**
   The dtrOutStream predicate relates the output stream of the original circuit
   to the  outstream of the transformed circuit. It insures that the original
   stream can be extracted from the outstream of the transformed circuit.
   dtrOutStream relates the stream S
                               i1:i2:i3:i4:....
   to the stream SS
                        _:_:_:i1x3:_:i2x3:_:i3x3:_:i4x3:
   The first two ouputs of SS are irrevelent (the circuit introduces a latency of two cycles
   to fill buffers), then the original values can be found at even places in triplets denoted
   ix3 where at least 2 values are i (i.e., are correct)
*)

CoInductive dtrOutStream : forall A, {|A|} -> Stream {|A|} -> Stream {|A#(A#A)|} -> Prop :=
| DtrOSt0 : forall A (a:{|A|}) z s s2,
            dtrOutStream1  a s s2 -> dtrOutStream  a s (Cons z s2)

with        dtrOutStream1 : forall A, {|A|} -> Stream {|A|} -> Stream {|A#(A#A)|} -> Prop :=
| DtrOSt1 : forall A (l a:{|A|}) lll s s2,
            atleast2 l lll -> dtrOutStream  a s s2 -> dtrOutStream1  l (Cons a s) (Cons lll s2).

(* ------------------------------------------------------------------------------------- *)
(* Evaluation of a circuit under SET(1,10) (with no glitch on primary inputs) *)
Definition set10_eval := setK_eval 10.

(* ------------------------------------------------------------------------------------- *)
(*   Main general lemma  *)

Lemma Dtrs_correct : forall S T (x c:circuit S T)  (cc:circuit S (T#(T#T))) i o o' n Pis Pos Pos2,
                       pureStream Pis -> pure_bset i -> pure_bset o -> pure_bset o'
                    -> Dtrs0 (ibs0 i) (obs0 o o') x c cc
                    -> step x i o c
                    -> eval c Pis Pos
                    -> set10_eval cc n (doublStream Pis) Pos2
                    -> dtrOutStream o Pos Pos2.
Proof.
cofix CIH. introv P1 P2 P3 P4 D S1 E H.
destruct Pis as [Pi Pis]. Inverts P1. Inverts E.
rewrite (unfold_Stream (doublStream _)) in H. cbn in H.
Inverts H.
- Apply step_Dtrs0 with D H8 in H11. SimpS.
  Inverts H12.
  + Rpure.
    Apply step_Dtrs1 with H0 H8 in H11; try apply pure_buildBus. SimpS.
    constructor. constructor. easy.
    apply CIH with (n:=pred (pred n)) (i:=Pi) (o:=Po) (o':=o) (x:=c) (c:=C') (cc:=c'0) (Pis:=Pis); easy.
  + Inverts H9. Inverts H12. Inverts H14. Inverts H15.
    Inverts H13. Inverts H18. Inverts H20. Inverts H21. Inverts H22.
    Inverts H23. Inverts H24. Inverts H25.
    do 4 (rewrite (unfold_Stream (doublStream _)) in H; cbn in H).
    Inverts H. Inverts H4. Inverts H7. Inverts H13. Inverts H15. Purestep H12 H14.
    eapply stepg_In1 in H11. 3: exact H0. 3: exact H8. 3: exact H10. 3: exact H9.
                             3: exact H12. 3: exact H14. 3: exact H17. 3: exact H19.
                             3: exact H18. 3: exact H20. 3: exact H21. 3: exact H22.
                             3: exact H23. 3: exact H24. 2: Rpure; CheckPure.
    destruct H11 as [?[?[?[?[? ?]]]]].
    do 5 (constructor; constructor; try easy).
    eapply CIH; try exact H27; try exact H16; try exact H26; try easy.
- Inverts H9. Inverts H7. Inverts H10. Inverts H13.
  Inverts H12. Inverts H17. Inverts H15. Inverts H19. Inverts H20.
  Inverts H21. Inverts H22. Inverts H23. Inverts H24.
  do 4 (rewrite (unfold_Stream (doublStream _)) in H; cbn in H).
  Inverts H. Inverts H4. Inverts H5. Inverts H12. Inverts H15.
  Purestep H8 H6 H9. Purestep H7 H10.
  eapply stepg_In0 in H11. 3: exact D. 3: exact S1. 3: exact H8. 3: exact H6. 3: exact H9.
                           3: exact H7. 3: exact H10. 3: exact H16. 3: exact H13.
                           3: exact H18. 3: exact H17. 3: exact H19. 3: exact H20.
                           3: exact H21. 3: exact H22. 3: exact H23. 2: CheckPure.
  destruct H11 as [?[?[?[?[? ?]]]]].
  do 5 (constructor; constructor; try easy).
  eapply CIH; try exact H26; try exact H25; try exact H14; try easy.
Qed.


(* ------------------------------------------------------------------------------------- *)
(** Initialisation of the IO buffers to false *)
Definition InputBuffersInit  S := ibs0 (buildBus S false).
Definition OutputBuffersInit T := obs0 (buildBus T false) (buildBus T false).

(*
Main theorem.
   The DTR transformation tolerates the SET(1,10) fault model provided :
   - no error occurs at the primary inputs (before the circuit)
   - no error occurs in the first two cycles (time needed to set buffers and checkpoints)
*)

Theorem DTR_correct : forall S T i0 o0 oo0 oo0' (c0 c1:circuit S T) cc cc1 n Pis Pos Pos2,
                      pureStream (Cons i0 Pis)
                   -> step c0 i0 o0 c1 -> eval c1 Pis Pos
                   -> step (DTR c0) i0 oo0 cc -> step cc i0 oo0' cc1
                   -> set10_eval cc1 n (doublStream Pis) Pos2
                   -> dtrOutStream (buildBus T false) (Cons o0 Pos) (Cons oo0 (Cons oo0' Pos2)).
Proof.
introv P S1 E SS1 SS2 H. Inverts P.
assert (R: Dtrs0 (InputBuffersInit  S) (OutputBuffersInit T) c0 c0 (DTR c0))
    by (constructor; eapply transf_dtr0; easy).
eapply step_Dtrs0 in R; try exact S1; try exact SS1; try apply pure_buildBus; try easy.
SimpS. Purestep S1.
eapply step_Dtrs1 in H1; try exact S1; try exact SS2; try apply pure_buildBus; try easy.
SimpS.
eapply Dtrs_correct in H1; try exact H; try exact E; try apply pure_buildBus; try easy.
do 2 constructor; easy.
Qed.

(* Print Assumptions DTR_correct. *)


(* Actually, it would be possible to tolerate errors even in the first two cycles.
   The initialization performed by the DTR transformation should be changed in order
   to put proper initial values in
   input/output buffers and memory blocks to authorize a valid roolback as soon as
   the second cycle*)
