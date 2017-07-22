
(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        Semantics of the Circuit Description Language     
#</h1>#    
-   Standard and Fault-model Semantics (Relational and Functional 
    when possible) 
#</center> <hr>#                                           *)
(*          Pascal Fradet - 2014_2015                      *)
(* ------------------------------------------------------- *)


 (* ######################################################## *)
(** * Standard and Fault-model Semantics of Programs        *)
(* ######################################################## *)

Require Export Syntax.

Set Implicit Arguments.

(* ####################################################### *)
(** *    Normal Execution  (Relational & Functional)       *)
(**      on buset (signals with glitches)                  *)
(* ####################################################### *)

(** ***       Relational Semantics of basic gates          *)

Inductive semgate: forall S T, gate S T -> {|S|} -> {|T|} -> Prop :=
| SNot : forall s, semgate Not s (negS s)
| SAnd : forall s, semgate And s (andS s)
| SOr  : forall s, semgate Or  s (orS s).

(*                     plugs                               *)
Inductive semplug: forall S T, plug S T -> {|S|} -> {|T|} -> Prop :=
| SPid : forall S s, semplug (@Pid S) s s
| SFork: forall S s, semplug (@Fork S) s {s,s}
| SSwap: forall S T s t, semplug (@Swap S T) {s,t} {t,s}
| SLsh : forall S T U s t u, semplug (@Lsh S T U) {{s,t},u} {s,{t,u}}
| SRsh : forall S T U s t u, semplug (@Rsh S T U) {s,{t,u}} {{s,t},u}.


(**           Functional Semantics of gates                *)

Definition redgate S T (g:gate S T): {|S|} -> {|T|} :=
match g with
(*                 Logic gates                             *)
| Not  => fun s => negS s
| And  => fun s => andS s
| Or   => fun s => orS  s
end.

(*          Functional Semantics of plugs                  *)
Definition redplug S T (p:plug S T): {|S|} -> {|T|} :=
match p with
| Pid _     => fun s => s
| Fork _    => fun s => {s,s}
| Swap _ _  => fun s => {sndS s,fstS s}
| Lsh _ _ _ => fun s => {fstS (fstS s), {sndS (fstS s),sndS s}}
| Rsh _ _ _ => fun s => {{fstS s, fstS (sndS s)},sndS (sndS s)}
end.

(***********************************************************)
(** **       Relational Semantics of Circuits              *)
(***********************************************************)

(** ***    Relational Semantics of circuits for one cycle  *)

Inductive step: forall S T, circuit S T -> {|S|} -> {|T|} -> circuit S T -> Prop :=
| Sgate: forall S T g s t, redgate g s = t -> step (@Cgate S T g) s t (@Cgate S T g)
| Splug: forall S T p s t, redplug p s = t -> step (@Cplug S T p) s t (@Cplug S T p)
| Sseq : forall S T U s t u c1 c2 c1' c2', step c1 s t c1'-> step c2 t u c2'
                                -> step (@Cseq S T U c1 c2) s u (@Cseq S T U c1' c2')
| Spar : forall S T U V s t u v c1 c2 c1' c2', 
         step c1 s t c1' -> step c2 u v c2'
      -> step (@Cpar S T U V c1 c2) {s,u} {t,v} (@Cpar S T U V c1' c2')
| Sloop: forall S T s t b b' a c c', 
         bset2bool a b'
      -> step c {s,bool2bset b} {t,a} c'
      -> step (@Cloop S T b c) s t (@Cloop S T b' c').
Hint Constructors step.

(** ***    Relational Semantics of circuits for streams   *)

CoInductive eval :forall S T, circuit S T -> Stream {|S|} -> Stream {|T|} -> Prop :=
| Coind_eval :  forall S T C C' Pi Pis Po Pos,
                @step S T C Pi Po C'  
             -> eval C' Pis Pos
             -> eval C (Cons Pi Pis) (Cons Po Pos).

(***********************************************************)
(** **         Functional Semantics of Circuits            *)
(*        defined only on pure signals (option)            *)
(***********************************************************)

(** ***    Functional reduction of combinatorial circuits   *)

Fixpoint redcomb S T (c: circuit S T ): {|S|} -> {|T|} :=
match c with
| Cgate g        => fun x => redgate g x
| Cplug p        => fun x => redplug p x
| Cseq c1 c2     => fun x => redcomb c2 (redcomb c1 x)
| Cpar c1 c2     => fun x => Pset (redcomb c1 (fstS x)) (redcomb c2 (sndS x))
| @Cloop s t b c => fun x => fstS (redcomb (c:circuit (Pbus s Wire) (Pbus t Wire))
                                          (Pset x (bool2bset b)))
end.

(** *    Functional semantics of circuits                  *)
(*     (fails if a glitch must be latched by a cell)       *)
Fixpoint fstep S T (c: circuit S T): {|S|} -> option ({|T|} * (circuit S T)):=
match c with
| Cgate g        => fun x => Some (redgate g x,Cgate g)
| Cplug  p       => fun x => Some (redplug p x,Cplug p)
| Cseq c1 c2     => fun x => match fstep c1 x with
                             | Some (x1,c1') => match fstep c2 x1 with
                                               | Some (x2,c2') => Some (x2,c1' -o- c2')
                                               | None          => None
                                                end
                             | None    => None
                             end
| Cpar c1 c2     => fun x => match fstep c1 (fstS x), fstep c2 (sndS x) with
                             | Some (x1,c1'), Some (x2,c2') => Some ({x1,x2},-|c1',c2'|-)
                             | _,_                          => None
                             end
| @Cloop s t b c => fun x => match @fstep (s#§) (t#§) c {x,bool2bset b} with
                             | Some (d,c') => match sndS d with
                                             | ~0 => Some (fstS d,-{false}-c')
                                             | ~1 => Some (fstS d,-{true}-c') 
                                             | ~? => None
                                             end
                             | None        => None
                             end
end.



(** *       Implementation of the SET(1,K) fault-model     *)
Section SET_1_K.

Variable K:nat.
(* ####################################################### *)
(** ** Introducting one glitch in one cycle                *)
(*   - introduced a glitch at all possible places/wires    *)
(*     i.e. at the primary inputs, after all logic gates   *)
(*   - used to implement the SET(1,K) fault-model          *)
(* ####################################################### *)

(* stepg may introduce a glitch after all logical gates or memory cells *)
Inductive stepg: forall S T, circuit S T -> {|S|} -> {|T|} -> circuit S T -> Prop :=
| Sgateg : forall S T g s t, introglitch (redgate g s) t -> stepg (@Cgate S T g) s  t (@Cgate S T g)
| Splugg : forall S T p s t, redplug p s = t -> stepg (@Cplug S T p) s t (@Cplug S T p)
| Sseqg1 : forall S T U s t u c1 c2 c1' c2', 
           stepg c1 s t c1'-> step c2 t u c2'
        -> stepg (@Cseq S T U c1 c2) s u (@Cseq S T U c1' c2')
| Sseqg2 : forall S T U s t u c1 c2 c1' c2', 
           step c1 s t c1'-> stepg c2 t u c2'
        -> stepg (@Cseq S T U c1 c2) s u (@Cseq S T U c1' c2')
| Sparg1 : forall S T U V s t u v c1 c2 c1' c2', 
           stepg c1 s t c1' -> step c2 u v c2'
        -> stepg (@Cpar S T U V c1 c2) {s,u} {t,v} (@Cpar S T U V c1' c2')
| Sparg2 : forall S T U V s t u v c1 c2 c1' c2', 
           step c1 s t c1' -> stepg c2 u v c2'
        -> stepg (@Cpar S T U V c1 c2) {s,u} {t,v} (@Cpar S T U V c1' c2')
| Sloopg1: forall S T s t b b' a c c', 
           bset2bool a b' 
        -> stepg c {s,bool2bset b} {t,a} c'
        -> stepg (@Cloop S T b c) s t (@Cloop S T b' c')
| Sloopg2: forall S T s t b bg b' a c c', 
          introglitch (bool2bset b) bg -> bset2bool a b' 
       -> step c {s,bg} {t,a} c'
       -> stepg (@Cloop S T b c) s t (@Cloop S T b' c').
Hint Constructors stepg.

(* stepglitch may introduce a glitch at the primary inputs or performs stepg *)
Inductive stepglitch: forall S T, circuit S T -> {|S|} -> {|T|} -> circuit S T -> Prop :=
| Satinput :  forall S T s s' t (c c':circuit S T), introglitch s s' -> step c s' t c' -> stepglitch c s t c'
| Safterlg :  forall S T s t    (c c':circuit S T), stepg c s t c' -> stepglitch c s t c'.

(** ** Evaluation of a circuit under the SET(1,K) fault-model     *)

(* glitch can be introduced even at the primary inputs *)
CoInductive set1K_eval :forall S T, circuit S T -> nat -> Stream {|S|} -> Stream {|T|} -> Prop :=
| set1K_eval1 : forall S T c c' Pi Pis Po Pos n,
                @step S T c Pi Po c'  
             -> set1K_eval c' (pred n) Pis Pos
             -> set1K_eval c n (Cons Pi Pis) (Cons Po Pos)
| set1K_eval2 : forall S T c c' Pi Pis Po Pos,
                @stepglitch S T c Pi Po c'  
             -> set1K_eval c' (pred K) Pis Pos
             -> set1K_eval c 0 (Cons Pi Pis) (Cons Po Pos).

(* Same but a glitch can only occur after a gate or a cell *)
(* used in the proof of DTR                                *)
CoInductive setK_eval :forall S T, circuit S T -> nat -> Stream {|S|} -> Stream {|T|} -> Prop :=
| setK_eval1 : forall S T c c' Pi Pis Po Pos n,
                @step S T c Pi Po c'  
             -> setK_eval c' (pred n) Pis Pos
             -> setK_eval c n (Cons Pi Pis) (Cons Po Pos)
| setK_eval2 : forall S T c c' Pi Pis Po Pos,
                @stepg S T c Pi Po c'  
             -> setK_eval c' (pred K) Pis Pos
             -> setK_eval c 0 (Cons Pi Pis) (Cons Po Pos).

(** **               Examples                                 *)
(* Evaluation of a circuit under the SET(1,2) fault-model     *)

CoInductive set12_eval :forall S T, circuit S T -> Stream {|S|} -> Stream {|T|} -> Prop :=
| Set12_eval1 : forall S T c c' Pi Pis Po Pos,
                @stepglitch S T c Pi Po c'  
             -> set12_eval' c' Pis Pos
             -> set12_eval c (Cons Pi Pis) (Cons Po Pos)

with        set12_eval' : forall S T, circuit S T -> Stream {|S|} -> Stream {|T|} -> Prop :=
| Set12_eval2 : forall S T c c' Pi Pis Po Pos,
                @step S T c Pi Po c'  
             -> set12_eval c' Pis Pos
             -> set12_eval' c (Cons Pi Pis) (Cons Po Pos).

(** ** Evaluation of a circuit under the SET(1,1) fault-model     *)

CoInductive set11_eval :forall S T, circuit S T -> Stream {|S|} -> Stream {|T|} -> Prop :=
| Set11_eval2 : forall S T c c' Pi Pis Po Pos,
                @stepglitch S T c Pi Po c'  
             -> set11_eval c' Pis Pos
             -> set11_eval c (Cons Pi Pis) (Cons Po Pos).

End SET_1_K.

(* ####################################################### *)
(** *    Functional semantics of circuits                  *)
(**      on busig (pure signals)                           *)
(* ####################################################### *)


(** **   Functional Semantics of gates and plugs on busig  *)
(*                 Logic gates                             *)
Definition redgateB S T (g:gate S T): [|S|] -> [|T|] :=
match g with
| Not  => fun s => negB s
| And  => fun s => andB s
| Or   => fun s => orB  s
end.

(*                 Plugs                                   *)
Definition redplugB S T (p:plug S T): [|S|] -> [|T|] :=
match p with
| Pid _     => fun s => s
| Fork _    => fun s => [s,s]
| Swap _ _  => fun s => [sndB s,fstB s]
| Lsh _ _ _ => fun s => [fstB (fstB s), [sndB (fstB s),sndB s]]
| Rsh _ _ _ => fun s => [[fstB s, fstB (sndB s)],sndB (sndB s)]
end.

(** **    Functional reduction of circuits on busig for one cycle  *)

Fixpoint fstepB S T (c: circuit S T ): [|S|] -> [|T|] * (circuit S T) :=
match c with
| Cgate g    => fun x => (redgateB g x,Cgate g)
| Cplug p    => fun x => (redplugB p x,Cplug p)
| Cseq c1 c2 => fun x => let (x1,c'1) := fstepB c1 x in
                                 let (x2,c'2) := fstepB c2 x1 in
                                 (x2, c'1 -o- c'2)
| Cpar c1 c2 => fun x => let (x1,c'1) := fstepB c1 (fstB x) in
                                 let (x2,c'2) := fstepB c2 (sndB x) in
                                 ([x1,x2],-|c'1,c'2|-)
| Cloop b c  => fun x => let (x',c') := fstepB c [x, bool2bsig b] in
                                 (fstB x', Cloop (bsig2bool (sndB x'))  c')
end.

(** **    Functional Semantics of circuits on streams of busig *)

CoFixpoint fevalB S T (c:circuit S T) : Stream [|S|] -> Stream [|T|] :=
fun I => match I with
         Cons i Is => let (o,c') := fstepB c i in
                      Cons o (fevalB c' Is)
         end.

