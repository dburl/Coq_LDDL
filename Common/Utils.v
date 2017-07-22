(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        Basic and simple tactics and notations
       (complements LibTactics) 
#</h1>#    
#</center> <hr>#                                           *)
(*          Pascal Fradet - 2014_2015                      *)
(* ------------------------------------------------------- *)

Require Export Bool BoolEq Arith List Streams LibTactics.

Set Implicit Arguments.


(* ####################################################### *)
(** *           Tactics and notations                      *)
(*  To annotate and structure proofs, we mostly use        *)
(*  the new "-,+,*" feature of Coq 8.4                     *)
(*                                                         *)
(*   We make use of LibTactics (introv, inverts, etc.)     *)
(*   and the following small shortcuts                     *)
(* ####################################################### *)

Ltac easy := solve [cbn; intros; auto].
(* Ltac easy := solve [simpl; intros; info_auto]. *)

Ltac dupl_base h1 h2 := generalize h1; intro h2.
Tactic Notation "dupl" hyp(H1)
                 ident(H2):= dupl_base H1 H2.
Tactic Notation "dupl" hyp(H1)
                 ident(H2) 
                 ident(H3):= dupl_base H1 H2; dupl H1 H3.
Tactic Notation "dupl" hyp(H1) 
                 ident(H2) 
                 ident(H3)
                 ident(H4):= dupl_base H1 H2; dupl H1 H3; dupl H1 H4.

Lemma eqfst: forall A B (a b:A*B), a=b -> fst a = fst b.
Proof. introv H. rewrite H. reflexivity. Qed.

Lemma eqsnd: forall A B (a b:A*B), a=b -> snd a = snd b.
Proof. introv H. rewrite H. reflexivity. Qed.

Lemma dpair : forall A B (x:A*B), exists f, exists s, x = (f,s).
Proof. introv. destruct x. exists a b. easy. Qed.

Ltac dstpair_base H Hf Hs :=  
dupl H Hf; apply eqfst in Hf; simpl in Hf;
dupl H Hs; apply eqsnd in Hs; simpl in Hs.

Tactic Notation "dstpair" hyp(H1) ident(H2) ident(H3) := dstpair_base H1 H2 H3.

Tactic Notation "dstpair" constr(E) ident(f) ident(s) ident(H) ident(Hf) ident(Hs)
              := destruct (dpair E) as [f [s H]]; dstpair_base H Hf Hs.


(* ####################################################### *)
(**               Notations                                *)
(* ####################################################### *)

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Notation "x ++ y" := (app x y) 
                     (at level 60, right associativity).
