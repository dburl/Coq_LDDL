
(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The triple modular redundancy transformation   
#</h1>#    

-  Definitions of the basic constituents  (protected control block, memory block)
-  Definition of the tmr transformation
-  Relation predicates between states of source and transformed circuits

              Pascal Fradet - Inria - 2014  
#</center> <hr>#       
                                                           *)
(* ------------------------------------------------------- *)
 
Add Rec LoadPath "..\Common\".

Require Export CirReflect.

 
Set Implicit Arguments.


(* ####################################################### *)
(** *    Some plugs used for parallel and loop operators   *)
(* ####################################################### *)


(** plug used before a triplicated parallel composition   *)

(** (((s,t) (s,t)),(s,t)) -> (((s,s),s),((t,t),t))     *)

Definition shuf1 s t : circuit (((s#t)#(s#t))#(s#t)) (((s#s)#s)#((t#t)#t))
           := -|shuffle s t s t,ID|--o-(shuffle (s#s) (t#t) s t).

(** plug used after a triplicated parallel composition   *)

(** (((s,s),s),((t,t),t)) ->  (((s,t) (s,t)),(s,t))      *)

Definition shuf2 s t : circuit (((s#s)#s)#((t#t)#t)) (((s#t)#(s#t))#(s#t)) 
           := (shuffle (s#s) s (t#t) t)-o--|shuffle s s t t,ID|-.

(** triplicated voters before a triplicated memory cell *)

Definition votmr s : circuit (((((s#s)#s)#§)#§)#§) (((s#§)#(s#§))#(s#§))
           := LSH -o- LSH -o- -|ID,RSH-o-Tvoter31|--o-(shuf2 s §).

(**  Reshuffling after a triplicated memory cell       *)

(** (((s,t) (s,t)),(s,t)) -> (((((s,s),s),t),t),t)     *) 

Definition shuf3 t : circuit (((t#§)#(t#§))#(t#§)) (((((t#t)#t)#§)#§)#§)
           := (shuf1 t §)-o-RSH-o--|RSH,ID|-.

(* ####################################################### *)
(** *   The Triple Modular Redundancy transformation       *) 
(**  It triplicates the circuit and inserts a triplicated  *)
(**  voter after each (triplicated) cell.                  *)
(* ####################################################### *)

Fixpoint tmr S T (c: circuit S T ): circuit ((S#S)#S) ((T#T)#T) :=
match c with
| Cgate g        => -|-|Cgate g, Cgate g|-, Cgate g|-
| Cplug g        => -|-|Cplug g, Cplug g|-, Cplug g|-
| Cseq c1 c2   => (tmr c1) -o- (tmr c2)
| @Cpar s t u v c1 c2 => (shuf1 s u)-o--|tmr c1,tmr c2|--o-(shuf2 t v)
| @Cloop s t b c      => -{b}-(-{b}-(-{b}-((votmr s)-o-(tmr c)-o-(shuf3 t))))
end.

(* ####################################################### *)
(** **    Triplicated signals and streams                  *)
(**           Used to express properties                   *)
(* ####################################################### *)

(** Voting between three signals                           *)

Definition vot31_sset (s1 s2 s3: sset) : {|§|} 
  := if (beq_sset s1 s2) || (beq_sset s1 s3) then (~s1)
     else if (beq_sset s2 s3) then (~s2) else (~Glitch). 

(**   Voting between three buses of signals               *)

Fixpoint voter31 S (s:{|S|}) (t:{|S|}) (u:{|S|}) : {|S|}.
destruct S; inversion s; inversion t; inversion u. 
- exact (vot31_sset H H0 H1).
- apply (Pset (voter31 S1 H1 H5 H9) (voter31 S2 H2 H6 H10)).
Defined.

(* Eval compute in (voter31 [~1,[~1,~1]] [~0,[~?,~1]]  [~1,[~1,~1]] ). *)

(**   Voting between three buses of signals in a bus   *)

(** Used to vote in the output stream of tmr(C)        *)

Definition voter_3_1 S (s:{|S#S#S|}) : {|S|}.
inversion s; inversion H1; exact (voter31 H2 H5 H6).
Defined.

(* Eval compute in (voter_3_1 [[~1,[~1,~1]],[~0,[~?,~1]], [~1,[~1,~1]]] ). *)


(**        Triplicating a stream of inputs               *)
CoFixpoint tmrStream S (Pis: Stream {|S|}) : Stream {|(S#S)#S|}:=
match Pis with  
Cons Pi Pis => Cons {{Pi,Pi},Pi} (tmrStream Pis)
end.

(** Merging a triplicated output stream by majority votes *)

CoFixpoint votStream S (Pot : Stream {|(S#S)#S|}) : Stream {|S|} :=
match Pot with  
Cons s3 Pots => Cons (voter_3_1 s3) (votStream Pots)
end.

(** * Definitions of corrupted triplicated codes and signals *)

(** Only the first one of the triplicated circuit (ie memory bank) is corrupted  *) 

Inductive corrupt_1in3_cir1 : forall S T, circuit S T -> circuit (S#S#S) (T#T#T) -> Prop :=
| Ccle11_1 : forall S T g, @corrupt_1in3_cir1 S T (Cgate g) (-| -| Cgate g, Cgate g |-, Cgate g |-)
| Ccle11_2 : forall S T p, @corrupt_1in3_cir1 S T (Cplug p) (-| -| Cplug p, Cplug p |-, Cplug p |-)
| Ccle11_3 : forall S T U c1 c2 ccc1 ccc2, 
             @corrupt_1in3_cir1 S T c1 ccc1 
          -> @corrupt_1in3_cir1 T U c2 ccc2
          -> corrupt_1in3_cir1 (c1-o-c2) (ccc1-o-ccc2)
| Ccle11_4 : forall S T U V c1 c2 ccc1 ccc2, 
             @corrupt_1in3_cir1 S T c1 ccc1 
          -> @corrupt_1in3_cir1 U V c2 ccc2
          -> corrupt_1in3_cir1 (-|c1,c2|-) ((shuf1 S U)-o--|ccc1,ccc2|--o-(shuf2 T V))
| Ccle11_5 : forall S T b x c ccc , 
             corrupt_1in3_cir1 c ccc
          -> corrupt_1in3_cir1 (-{b}-c) (-{x}-(-{b}-(-{b}-((votmr S)-o-(ccc)-o-(shuf3 T))))).
Hint Constructors corrupt_1in3_cir1.

(** Only the second one of the triplicated circuit (ie memory bank) is corrupted  *) 

Inductive corrupt_1in3_cir2 : forall S T, circuit S T -> circuit (S#S#S) (T#T#T) -> Prop :=
| Ccle12_1 : forall S T g, @corrupt_1in3_cir2 S T (Cgate g) (-| -| Cgate g, Cgate g |-, Cgate g |-)
| Ccle12_2 : forall S T p, @corrupt_1in3_cir2 S T (Cplug p) (-| -| Cplug p, Cplug p |-, Cplug p |-)
| Ccle12_3 : forall S T U c1 c2 ccc1 ccc2, 
             @corrupt_1in3_cir2 S T c1 ccc1 
          -> @corrupt_1in3_cir2 T U c2 ccc2
          -> corrupt_1in3_cir2 (c1-o-c2) (ccc1-o-ccc2)
| Ccle12_4 : forall S T U V c1 c2 ccc1 ccc2, 
             @corrupt_1in3_cir2 S T c1 ccc1 
          -> @corrupt_1in3_cir2 U V c2 ccc2
          -> corrupt_1in3_cir2 (-|c1,c2|-) ((shuf1 S U)-o--|ccc1,ccc2|--o-(shuf2 T V))
| Ccle12_5 : forall S T b x c ccc , 
             corrupt_1in3_cir2 c ccc
          -> corrupt_1in3_cir2 (-{b}-c) (-{b}-(-{x}-(-{b}-((votmr S)-o-(ccc)-o-(shuf3 T))))).
Hint Constructors corrupt_1in3_cir2.

(** Only the third one of the triplicated circuit (ie memory bank) is corrupted  *) 

Inductive corrupt_1in3_cir3 : forall S T, circuit S T -> circuit (S#S#S) (T#T#T) -> Prop :=
| Ccle13_1 : forall S T g, @corrupt_1in3_cir3 S T (Cgate g) (-| -| Cgate g, Cgate g |-, Cgate g |-)
| Ccle13_2 : forall S T p, @corrupt_1in3_cir3 S T (Cplug p) (-| -| Cplug p, Cplug p |-, Cplug p |-)
| Ccle13_3 : forall S T U c1 c2 ccc1 ccc2, 
             @corrupt_1in3_cir3 S T c1 ccc1 
          -> @corrupt_1in3_cir3 T U c2 ccc2
          -> corrupt_1in3_cir3 (c1-o-c2) (ccc1-o-ccc2)
| Ccle13_4 : forall S T U V c1 c2 ccc1 ccc2, 
             @corrupt_1in3_cir3 S T c1 ccc1 
          -> @corrupt_1in3_cir3 U V c2 ccc2
          -> corrupt_1in3_cir3 (-|c1,c2|-) ((shuf1 S U)-o--|ccc1,ccc2|--o-(shuf2 T V))
| Ccle13_5 : forall S T b x c ccc , 
             corrupt_1in3_cir3 c ccc
          -> corrupt_1in3_cir3 (-{b}-c) (-{b}-(-{b}-(-{x}-((votmr S)-o-(ccc)-o-(shuf3 T))))).
Hint Constructors corrupt_1in3_cir3.

(** Only  one of the triplicated circuit (ie memory bank) is corrupted  *) 

Inductive corrupt_1in3_cir : forall S T, circuit S T -> circuit (S#S#S) (T#T#T) -> Prop :=
| Ccle1_1 : forall S T c ccc, @corrupt_1in3_cir1 S T c ccc -> corrupt_1in3_cir c ccc 
| Ccle1_2 : forall S T c ccc, @corrupt_1in3_cir2 S T c ccc -> corrupt_1in3_cir c ccc 
| Ccle1_3 : forall S T c ccc, @corrupt_1in3_cir3 S T c ccc -> corrupt_1in3_cir c ccc.
Hint Constructors corrupt_1in3_cir.

(** Only the first one of the triplicated buses of signals is corrupted   *) 

Inductive corrupt_1in3_bus1 : forall S, {|S|} -> {|(S#S)#S|} -> Prop :=
| Csle1_11 : forall S s t, @corrupt_1in3_bus1 S s {t,s,s}.
Hint Constructors corrupt_1in3_bus1.

(** Only the second one of the triplicated buses of signals is corrupted  *) 

Inductive corrupt_1in3_bus2 : forall S, {|S|} -> {|(S#S)#S|} -> Prop :=
| Csle1_12 : forall S s t, @corrupt_1in3_bus2 S s {s,t,s}.
Hint Constructors corrupt_1in3_bus2.

(** Only the third one of the triplicated buses of signals is corrupted   *) 

Inductive corrupt_1in3_bus3 : forall S, {|S|} -> {|(S#S)#S|} -> Prop :=
| Csle1_13 : forall S s t, @corrupt_1in3_bus3 S s {s,s,t}.
Hint Constructors corrupt_1in3_bus3.

(**     Only one of the triplicated buses of signals is corrupted        *) 

Inductive corrupt_1in3_bus : forall S, {|S|} -> {|S#S#S|} -> Prop :=
| Csle1_1 : forall S s t, @corrupt_1in3_bus S s {s,s,t}
| Csle1_2 : forall S s t, @corrupt_1in3_bus S s {s,t,s}
| Csle1_3 : forall S s t, @corrupt_1in3_bus S s {t,s,s}.
Hint Constructors corrupt_1in3_bus.

(** A stream has at most one of its triplicated element corrupted  *)

CoInductive corrupt_1in3_stream : forall S, Stream {|S|} -> Stream {|S#S#S|} -> Prop :=
| Coind_scle1 : forall S s xs sss xsss, @corrupt_1in3_bus S s sss 
                                     -> corrupt_1in3_stream xs xsss 
                                     -> corrupt_1in3_stream (Cons s xs) (Cons sss xsss).

(* ####################################################### *)
(** *  Some lemmas on  corrupt_1in3_cir                    *) 
(* ####################################################### *)

Lemma ccir_seq : forall S T U (c1:circuit S T) (c2:circuit T U)  ccc, 
                    corrupt_1in3_cir (c1 -o- c2) ccc
                 -> exists ccc1 ccc2,ccc=ccc1 -o-ccc2 /\ corrupt_1in3_cir c1 ccc1 /\ corrupt_1in3_cir c2 ccc2.
Proof. 
introv C. Inverts C; Inverts H3; exists ccc1 ccc2; easy. 
Qed.

Lemma ccir_par : forall S T U V (c1:circuit S T) (c2:circuit U V) ccc, 
                    corrupt_1in3_cir (-|c1 , c2|-) ccc
                 -> exists ccc1 ccc2, (ccc = (shuf1 S U)-o- -|ccc1,ccc2|--o-(shuf2 T V) )
                   /\ corrupt_1in3_cir c1 ccc1 /\ corrupt_1in3_cir c2 ccc2.
Proof. 
introv C. Inverts C; Inverts H3; exists ccc1 ccc2; easy. 
Qed.

Lemma ccir_loop : forall S T (c:circuit (S#§) (T#§)) b ccc, 
                    corrupt_1in3_cir (-{b}-c) ccc
                 -> exists b1 b2 b3 ccc1, (ccc = -{b1}-(-{b2}-(-{b3}-((votmr S)-o-ccc1-o-(shuf3 T)))))
                   /\ corrupt_1in3_bus (bool2bset b) {bool2bset b1,bool2bset b2,bool2bset b3} 
                   /\ corrupt_1in3_cir c ccc1.
Proof. 
introv C. Inverts C; Inverts H3.
- exists x b b ccc0. easy.
- exists b x b ccc0. easy.
- exists b b x ccc0. easy.
Qed.

