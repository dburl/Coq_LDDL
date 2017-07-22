
(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        Simple Circuit Description Language     
#</h1>#    
-   Syntax and some useful small circuits 
#</center> <hr>#                                           *)
(*          Pascal Fradet - 2014_2015                      *)
(* ------------------------------------------------------- *)

Require Import Omega. 
Require Export Signals.

Set Implicit Arguments.

(* ####################################################### *)
(** *            Syntax of circuits                        *)
(* ####################################################### *)

(* ####################################################### *)
(** **                    Logic gates                      *)
(* ####################################################### *)

Inductive gate : bus -> bus -> Set := 
| Not : gate § §
| And : gate (§#§) §
| Or  : gate (§#§) §.


(** A dependent destruction for gates without axioms *)

(* the general destruction lemma for gates *)
Lemma gate_case :
  forall S T (P : gate S T -> Type),
    (forall (pf : (§,§)=(S,T)), P (eq_rect (§,§)  (fun s => gate (fst s) (snd s)) (Not) (S,T) pf)) -> 
    (forall (pf : (§#§,§)=(S,T)), P (eq_rect (§#§,§) (fun s => gate (fst s) (snd s)) (And) (S,T) pf)) -> 
    (forall (pf : (§#§,§)=(S,T)), P (eq_rect (§#§,§) (fun s => gate (fst s) (snd s)) (Or)  (S,T) pf)) -> 
    (forall x, P x).
Proof.
intros.
destruct x.
- specialize (X  eq_refl). 
  rewrite <- Eqdep_dec.eq_rect_eq_dec in X by (decide equality; apply eqdec_bus).
  easy.
- specialize (X0 eq_refl).
  rewrite <- Eqdep_dec.eq_rect_eq_dec in X0 by (decide equality; apply eqdec_bus).
  easy.
- specialize (X1 eq_refl).
  rewrite <- Eqdep_dec.eq_rect_eq_dec in X1 by (decide equality; apply eqdec_bus).
  easy.
Qed.

(* special case : Not *)
Lemma unary_gate : forall (P : gate § § -> Type), (P Not) -> (forall x, P x).
Proof. 
intros.
apply gate_case; intros. 
- rewrite <- Eqdep_dec.eq_rect_eq_dec by (decide equality; apply eqdec_bus).
  apply X.
- Inverts pf.
- Inverts pf.
Qed.

(* special case : And, Or  *)
Lemma binary_gate : forall (P : gate (§#§) § -> Type), (P And) -> (P Or) -> (forall x, P x).
Proof. 
intros.
apply gate_case; intros.
- Inverts pf. 
- rewrite <- Eqdep_dec.eq_rect_eq_dec by (decide equality; apply eqdec_bus).
  apply X.
- rewrite <- Eqdep_dec.eq_rect_eq_dec by (decide equality; apply eqdec_bus).
  apply X0.
Qed.

Ltac case_gate g :=
match type of g with
| gate § §     => apply unary_gate
| gate (§#§) § => apply binary_gate
| _            =>  apply gate_case; intro _pf; inversion _pf; subst; 
                  rewrite <- Eqdep_dec.eq_rect_eq_dec by (decide equality; apply eqdec_bus)
end.

Ltac ddestruct_g_base g :=  
     repeat  match goal with
           | H : context[g] |- _ => revert H
             end;    
             pattern g; case_gate g; clear g.


Tactic Notation "Destruct_g" hyp(g) :=
   ddestruct_g_base g; intros.

(* Equality of gates is decidable *)
Lemma eqdec_gate S T (g1 g2:gate S T) : sumbool (g1=g2) (g1 <> g2). (* notation issue : {s=t} + {s<>t} %type *)
Proof.
destruct g1; Destruct_g g2; 
try (solve [right; intro X; Inverts X]); try (left; easy).
Qed.

(*      syntactic equality of gates          *)
Fixpoint beq_gate S T U V (g1:gate S T) (g2:gate U V): bool :=
match g1,g2 with
| Not , Not  => true
| And , And  => true
| Or  , Or   => true
|  _  , _    => false
end.

(** Syntactic equality of gates and input bus implies equality of output buses *)
Lemma beq_gate_eq_out : forall S T U (g1:gate S T) (g2:gate S U),
                        beq_gate g1 g2 = true -> T=U.
Proof.
introv H. destruct g1; Destruct_g g2; easy.
Qed.

(** Syntactic equality of gates and types implies equality of gates *)
Lemma beq_gate_imp_eq : forall S T (g1 g2:gate S T), beq_gate g1 g2 = true -> g1=g2.
Proof.
induction g1; introv H; Destruct_g g2; Inverts H; try easy.
Qed.

Lemma beq_gate_reflx : forall S T (g:gate S T), beq_gate g g = true.
Proof.
destruct g; easy.
Qed.


(* ####################################################### *)
(** **                  Plugs                              *)
(* ####################################################### *)
(**               Wiring primitives                        *)
Inductive plug : bus -> bus -> Set := 
| Pid : forall S, plug S S
| Fork: forall S, plug S (S#S)
| Swap: forall S T, plug (S#T) (T#S)
| Lsh : forall S T U, plug ((S#T)#U) (S#(T#U))
| Rsh : forall S T U, plug (S#(T#U)) ((S#T)#U).


(** A dependent destruction for plugs without axioms *)

(* the general destruction lemma for plugs *)

(* the general destruction lemma for plugs *)

Lemma plug_case :
  forall S T (P : plug S T -> Type),
    (forall A (_pf : (A,A)=(S,T)), 
            P (eq_rect (A,A)  (fun s => plug (fst s) (snd s)) (Pid A) (S,T) _pf)) -> 
    (forall A (_pf : (A,A#A)=(S,T)), 
            P (eq_rect (A,A#A) (fun s => plug (fst s) (snd s)) (Fork A) (S,T) _pf)) -> 
    (forall A B (_pf : (A#B,B#A)=(S,T)),
            P (eq_rect (A#B,B#A) (fun s => plug (fst s) (snd s)) (Swap A B)  (S,T) _pf)) -> 
    (forall A B C (_pf : ((A#B)#C,A#(B#C))=(S,T)), 
            P (eq_rect ((A#B)#C,A#(B#C)) (fun s => plug (fst s) (snd s)) (Lsh A B C)  (S,T) _pf)) -> 
    (forall A B C (_pf : (A#(B#C),(A#B)#C)=(S,T)), 
            P (eq_rect (A#(B#C),(A#B)#C) (fun s => plug (fst s) (snd s)) (Rsh A B C)  (S,T) _pf)) -> 
    (forall x, P x).
Proof.
intros.
destruct x.
- specialize (X S eq_refl). 
  rewrite <- Eqdep_dec.eq_rect_eq_dec in X by (decide equality; apply eqdec_bus).
  easy.
- specialize (X0 S eq_refl).
  rewrite <- Eqdep_dec.eq_rect_eq_dec in X0 by (decide equality; apply eqdec_bus).
  easy.
- specialize (X1 S T eq_refl).
  rewrite <- Eqdep_dec.eq_rect_eq_dec in X1 by (decide equality; apply eqdec_bus).
  easy.
- specialize (X2 S T U eq_refl).
  rewrite <- Eqdep_dec.eq_rect_eq_dec in X2 by (decide equality; apply eqdec_bus).
  easy.
- specialize (X3 S T U eq_refl).
  rewrite <- Eqdep_dec.eq_rect_eq_dec in X3 by (decide equality; apply eqdec_bus).
  easy.
Qed.

Ltac case_plug p := 
     apply plug_case; intros; inversion _pf; try subst;
     try (rewrite <- Eqdep_dec.eq_rect_eq_dec by (decide equality; apply eqdec_bus));
     try (
     match goal with
   | H : context[eq_rect] |- _ =>  rewrite <- Eqdep_dec.eq_rect_eq_dec in H  by (decide equality; apply eqdec_bus)
     end).

(* rewrite <- Eqdep_dec.eq_rect_eq_dec by (decide equality; apply eqdec_bus). *)

Ltac ddestruct_p_base p :=  
     repeat  match goal with
           | H : context[p] |- _ => revert H
             end;    
             pattern p; case_plug p; clear p.


Tactic Notation "Destruct_p" hyp(p) := ddestruct_p_base p; intros.

(**             Equality of plugs             *)

(* Equality of plugs is decidable             *)


Lemma eqdec_plug S T (p1 p2:plug S T) : sumbool (p1=p2) (p1 <> p2). (* notation issue : {s=t} + {s<>t} %type *)
Proof.
destruct p1; pattern p2; Destruct_p p2; try easy.
- rewrite H0 in H1. symmetry in H1; apply S_diff_S_T in H1; false.
- Inverts H1. 
  rewrite <- Eqdep_dec.eq_rect_eq_dec by (decide equality; apply eqdec_bus).
  right; intro G1; Inverts G1.
- Inverts H1 as H1.  apply S_diff_S_T in H1; false.
- Inverts H1 as H1. symmetry in H1; apply S_diff_S_T in H1; false.
- apply S_diff_S_T in H1; false. 
- rewrite <- H0 in H2. apply S_diff_S_T in H2; false.
- rewrite <- H2 in H0. Inverts H0. 
  symmetry in H3. apply S_diff_T_S in H3; false.
- Inverts H0. symmetry in H1. apply S_diff_S_T in H1; false.
- Inverts H1. rewrite <- Eqdep_dec.eq_rect_eq_dec by (decide equality; apply eqdec_bus).
  right; intro G1; Inverts G1.
- symmetry in H1. apply S_diff_T_S in H1; false.
- Inverts H3. rewrite <- Eqdep_dec.eq_rect_eq_dec by (decide equality; apply eqdec_bus).
  right; intro G1; Inverts G1.
- Inverts H1. rewrite <- Eqdep_dec.eq_rect_eq_dec by (decide equality; apply eqdec_bus).
  right; intro G1; Inverts G1.
- Inverts H1. symmetry in H0. apply S_diff_S_T in H0; false.
- Inverts H2. symmetry in H0. apply S_diff_T_S in H0; false.
- Inverts H3. rewrite <- Eqdep_dec.eq_rect_eq_dec by (decide equality; apply eqdec_bus).
  right; intro G1; Inverts G1.
- rewrite H0 in H2.
  assert (X:depth_bus S = depth_bus ((S#T)#B)) by (rewrite H2; easy).
  cbn in X. omega. 
- Inverts H1 as G1 G2. apply S_diff_S_T in G1; false.
- Inverts H1 as G1 G2. symmetry in G1. apply S_diff_S_T in G1; false.
- Inverts H2. rewrite <- Eqdep_dec.eq_rect_eq_dec by (decide equality; apply eqdec_bus).
  right; intro G1; Inverts G1.
- rewrite H2 in H0.
  assert (X:depth_bus S = depth_bus ((S#T)#B)) by (rewrite H0; easy).
  cbn in X. omega.
Qed.

(* syntactic equality of plugs (not checking types) *)
Fixpoint beq_plug S T U V (p1:plug S T) (p2:plug U V): bool :=
match p1,p2 with
| Pid _ , Pid _          => true
| Fork _ , Fork _        => true
| Swap _ _ , Swap _ _    => true
| Lsh _ _ _ , Lsh _ _ _  => true
| Rsh _ _ _ , Rsh _ _ _  => true
|  _  , _  => false
end.

(** Syntactic equality of gates and input bus implies equality of output buses *)
Lemma beq_plug_eq_out : forall S T U (p1:plug S T) (p2:plug S U),
                        beq_plug p1 p2 = true -> T=U.
intros. destruct p1; Destruct_p p2; Inverts H; try easy.
- induction S; Inverts H1.
- induction U; Inverts H1.
Qed.

(** Syntactic equality of gates and types implies equality of gates *)

Lemma beq_plug_imp_eq : forall S T (p1 p2:plug S T), beq_plug p1 p2 = true -> p1=p2.
Proof.
induction p1; introv H; Destruct_p p2; try easy.
- Inverts H2. symmetry in H0; apply S_diff_T_S in H0; false.
- Inverts H2.
  rewrite <- Eqdep_dec.eq_rect_eq_dec  in H by (decide equality; apply eqdec_bus).
  Inverts H.
- Inverts H2. apply S_diff_S_T in H1; false.
- Inverts H2. apply S_diff_T_S in H3; false.
- apply S_diff_S_T in H2; false.
- rewrite <- H1 in H3. apply S_diff_S_T in H3; false.
- Inverts H1. Inverts H3. apply S_diff_T_S in H4; false.
- Inverts H1. symmetry in H2. apply S_diff_S_T in H2; false.
- Inverts H2. rewrite <- Eqdep_dec.eq_rect_eq_dec  in H by (decide equality; apply eqdec_bus).
  Inverts H.
- symmetry in H3. apply S_diff_S_T in H3; false.
- Inverts H4. rewrite <- Eqdep_dec.eq_rect_eq_dec  in H by (decide equality; apply eqdec_bus).
  Inverts H.
- Inverts H2. rewrite <- Eqdep_dec.eq_rect_eq_dec  in H by (decide equality; apply eqdec_bus).
  Inverts H.
- Inverts H2. apply S_diff_T_S in H3; false.
- Inverts H3. symmetry in H1. apply S_diff_T_S in H1; false.
- Inverts H4. rewrite <- Eqdep_dec.eq_rect_eq_dec  in H by (decide equality; apply eqdec_bus).
  Inverts H.
- rewrite H1 in H3. assert (X:depth_bus S = depth_bus ((S#T)#B)) by (rewrite H3; easy).
  cbn in X. omega.
- Inverts H2. apply S_diff_S_T in H1; false.
- Inverts H2. symmetry in H1. apply S_diff_S_T in H1; false.
- Inverts H3. rewrite <- Eqdep_dec.eq_rect_eq_dec  in H by (decide equality; apply eqdec_bus).
  Inverts H.
- rewrite H3 in H1. assert (X:depth_bus S = depth_bus ((S#T)#B)) by (rewrite H1; easy).
  cbn in X. omega.
Qed.

Lemma beq_plug_reflx : forall S T (p:plug S T), beq_plug p p = true.
Proof.
destruct p; try easy.
- induction S; easy.
- induction S; easy.
Qed.


(* ####################################################### *)
(** **                  Circuits                           *)
(* ####################################################### *)

Inductive circuit : bus -> bus -> Set :=
| Cgate : forall S T, gate S T -> circuit S T
| Cplug : forall S T, plug S T -> circuit S T
| Cseq  : forall S T U, circuit S T -> circuit T U -> circuit S U
| Cpar  : forall S T U V, circuit S T -> circuit U V -> circuit (S#U) (T#V)
| Cloop : forall S T, bool -> circuit (S#§) (T#§) -> circuit S T.

(** A dependent destruction for circuits without axioms *)
(* the general destruction lemma for circuits *)

Lemma circuit_case :
  forall S T (P : circuit S T -> Type),
    (forall (g:gate S T), P (Cgate g)) -> 
    (forall (g:plug S T), P (Cplug g)) -> 
    (forall U (c1:circuit S U) (c2:circuit U T), P (Cseq c1 c2)) ->
    (forall S1 S2 T1 T2 (c1:circuit S1 T1) (c2:circuit S2 T2) (_pf : (S1#S2,T1#T2)=(S,T)),
            P (eq_rect (S1#S2,T1#T2) (fun s => circuit (fst s) (snd s)) (Cpar c1 c2)  (S,T) _pf)) -> 
    (forall (b:bool) (c:circuit (S#§) (T#§)), P (Cloop b c)) -> 
    (forall x, P x).
Proof.
introv ? ? ? H ?.
destruct x as [?|?|?|S T U V c1 c2|?]; try easy.
- specialize (H S U T V c1 c2 eq_refl). 
  rewrite <- Eqdep_dec.eq_rect_eq_dec in H by (decide equality; apply eqdec_bus).
  easy.
Qed.

Ltac case_circuit c := 
     apply circuit_case; intros; try inversion _pf; try subst;
     try (rewrite <- Eqdep_dec.eq_rect_eq_dec by (decide equality; apply eqdec_bus));
     try (
     match goal with
   | H : context[eq_rect] |- _ =>  rewrite <- Eqdep_dec.eq_rect_eq_dec in H  by (decide equality; apply eqdec_bus)
     end).

(* rewrite <- Eqdep_dec.eq_rect_eq_dec by (decide equality; apply eqdec_bus). *)

Ltac ddestruct_c_base c :=  
     repeat  match goal with
           | H : context[c] |- _ => revert H
             end;    
             pattern c; case_circuit c; clear c.


Tactic Notation "Destruct_c" hyp(c) := ddestruct_c_base c; intros.



Lemma eqdec_circuit S T (c1 c2:circuit S T) : sumbool (c1 = c2) (c1 <> c2). (* {s=t} + {s<>t} %type *)
Proof.
induction c1.
- destruct c2; try (solve [right; intro H; Inverts H]).
  destruct (eqdec_gate g g0).
  left. subst. easy.
  right. intro H. apply n. Inverts H. easy.
- destruct c2; try (solve [right; intro H; Inverts H]).
  destruct (eqdec_plug p p0).
  left. subst. easy.
  right. intro H. apply n. Inverts H. easy.
- destruct c2; try (solve [right; intro H; Inverts H]).
  destruct (eqdec_bus T T0). 
  + subst. destruct (IHc1_1 c2_1); destruct (IHc1_2 c2_2); subst;
    try (right; intro H; apply n; Inverts H; easy).
    left. easy.
  + right. intro H. Inverts H. apply n. easy.
- Destruct_c c2; try (solve [right; intro H; Inverts H]).
  destruct (IHc1_1 c1); destruct (IHc1_2 c0); subst;
  try (right; intro H; apply n; Inverts H; easy). easy. 
- destruct c2; try (solve [right; intro H; Inverts H]). 
  destruct (bool_dec b b0); destruct (IHc1 c2); subst;
  try (right; intro H; apply n; Inverts H; easy).
  left; easy.
Defined.

(** syntactic equality of circuits (not checking types) *)
Fixpoint beq_circuit S T U V (c1:circuit S T) (c2:circuit U V): bool :=
match c1,c2 with
| Cgate g1, Cgate g2       => beq_gate g1 g2 
| Cplug p1, Cplug p2       => beq_plug p1 p2 
| Cseq d1 d2, Cseq e1 e2   => (beq_circuit d1 e1) && (beq_circuit d2 e2)
| Cpar d1 d2, Cpar e1 e2   => (beq_circuit d1 e1) && (beq_circuit d2 e2)
| Cloop b1 d1, Cloop b2 d2 => (eqb b1 b2) && (beq_circuit d1 d2)
|  _   , _                 => false
end.

(** Syntactic equality of circuits and input bus implies equality of output buses *)

Lemma beq_cir_eq_out : forall S T (c1:circuit S T) U (c2:circuit S U), beq_circuit c1 c2 = true -> T=U.
induction c1; introv H; Destruct_c c2; Inverts H.
- apply beq_gate_eq_out in H1. easy.
- apply beq_plug_eq_out in H1. easy.
- apply andb_prop in H1. destruct H1 as [H1 H2].
  apply IHc1_1 in H1. subst. apply IHc1_2 in H2. easy.
- apply andb_prop in H1. destruct H1 as [H1 H2].
  apply IHc1_1 in H1. subst. apply IHc1_2 in H2. subst. easy.
- apply andb_prop in H1. destruct H1 as [H1 H2].
  apply IHc1 in H2. subst. Inverts H2. easy.
Qed.

(** Syntactic equality of circuits and types implies equality of gates *)
Lemma beq_circuit_imp_eq : forall S T (x y:circuit S T), beq_circuit x y=true -> x=y.
Proof.
induction x; introv H; Destruct_c y; Inverts H.
- apply beq_gate_imp_eq in H1. subst. easy.
- apply beq_plug_imp_eq in H1. subst. easy.
- apply andb_prop in H1. destruct H1 as [H1 H2].
  destruct (eqdec_bus T U0). 
  + subst. apply IHx1 in H1. apply IHx2 in H2. subst. easy.
  + apply beq_cir_eq_out in H1. false.
- apply andb_prop in H1. destruct H1 as [H1 H2].
  apply IHx1 in H1. apply IHx2 in H2. subst. easy.
- apply andb_prop in H1. destruct H1 as [H1 H2].
  apply IHx in H2. apply eqb_prop in H1. 
  subst. easy.
Qed.

Lemma beq_circuit_reflx : forall S T (c:circuit S T), beq_circuit c c =true.
Proof.
induction c; cbn.
- apply beq_gate_reflx.
- apply beq_plug_reflx.
- rewrite IHc1. rewrite IHc2. easy. 
- rewrite IHc1. rewrite IHc2. easy. 
- rewrite IHc. rewrite eqb_reflx. easy.
Qed. 


(* ####################################################### *)
(** **                  Notations                          *)
(* ####################################################### *)

Notation "'NOT'"       := (Cgate Not) (at level 40).
Notation "'AND'"       := (Cgate And) (at level 40).
Notation "'OR'"        := (Cgate Or) (at level 40).
Notation "'ID'"        := (Cplug (Pid _)) (at level 40).
Notation "'FORK'"      := (Cplug (Fork _)) (at level 40).
Notation "'SWAP'"      := (Cplug (Swap _ _)) (at level 40).
Notation "'LSH'"       := (Cplug (Lsh _ _ _)) (at level 40).
Notation "'RSH'"       := (Cplug (Rsh _ _ _)) (at level 40).
Notation "-| X , Y |-" := (Cpar X Y)   (at level 50).
Notation "-{ X }- C"   := (Cloop X C)   (at level 60, X ident).
Notation "X '-o-' Y"   := (Cseq X Y)   (at level 0).

(** **              Classes of circuits                *)

Inductive combinatorial : forall S T, circuit S T -> Prop :=
| Combgate: forall S T g, combinatorial (@Cgate S T g)
| Combplug: forall S T p, combinatorial (@Cplug S T p)
| Combseq : forall S T U c1 c2, 
            combinatorial c1 -> combinatorial c2 -> combinatorial (@Cseq S T U c1 c2)
| Combpar : forall S T U V c1 c2, 
            combinatorial c1 -> combinatorial c2 -> combinatorial (@Cpar S T U V c1 c2).
Hint Constructors combinatorial.

Fixpoint is_comb S T (c: circuit S T ): bool :=
match c with
| Cgate g    => true
| Cplug g    => true
| Cseq c1 c2 => andb (is_comb c1) (is_comb c2)
| Cpar c1 c2 => andb (is_comb c1) (is_comb c2)
| Cloop b c  => false
end.

Lemma comb_equiv_is_comb : forall S T (c:circuit S T), combinatorial c <-> is_comb c = true.
Proof.
split.
- introv H. induction H.
  + easy.
  + easy.
  + cbn. rewrite IHcombinatorial1. rewrite IHcombinatorial2. easy.
  + cbn. rewrite IHcombinatorial1. rewrite IHcombinatorial2. easy.
- introv H. induction c as [?|?|? ? ? ? IH1 ? IH2|? ? ? ? ? IH1 ? IH2|?].
  + constructor.
  + constructor. 
  + cbn in H. apply andb_true_iff in H. destruct H as [H1 H2]. 
    apply IH1 in H1. apply IH2 in H2. constructor; easy.
  + cbn in H. apply andb_true_iff in H. destruct H as [H1 H2]. 
    apply IH1 in H1. apply IH2 in H2. constructor; easy.
  + Inverts H.
Qed.


Inductive wiring : forall S T, circuit S T -> Prop :=
| Pplug: forall S T p, wiring (@Cplug S T p)
| Pseq : forall S T U c1 c2, 
            wiring c1 -> wiring c2 -> wiring (@Cseq S T U c1 c2)
| Ppar : forall S T U V c1 c2, 
            wiring c1 -> wiring c2 -> wiring (@Cpar S T U V c1 c2).
Hint Constructors wiring.

Fixpoint is_wiring S T (c: circuit S T ): bool :=
match c with
| Cgate g    => false
| Cplug  g   => true
| Cseq c1 c2 => andb (is_wiring c1) (is_wiring c2)
| Cpar c1 c2 => andb (is_wiring c1) (is_wiring c2)
| Cloop b c  => false
end.

Lemma wiring_equiv_is_wiring : forall S T (c:circuit S T), wiring c <-> is_wiring c = true.
Proof.
split.
- introv H. induction H.
  + easy.
  + cbn. rewrite IHwiring1. rewrite IHwiring2. easy.
  + cbn. rewrite IHwiring1. rewrite IHwiring2. easy.
- introv H. induction c; Inverts H; constructor;
  apply andb_true_iff in H1; destruct H1; easy. 
Qed.

Inductive sequential : forall S T, circuit S T -> Prop :=
| Seqseql : forall S T U c1 c2, 
            sequential c1 -> sequential (@Cseq S T U c1 c2)
| Seqseqr : forall S T U c1 c2, 
            sequential c2 -> sequential (@Cseq S T U c1 c2)
| Seqparl : forall S T U V c1 c2, 
            sequential c1 -> sequential (@Cpar S T U V c1 c2)
| Seqparr : forall S T U V c1 c2, 
            sequential c2 -> sequential (@Cpar S T U V c1 c2)
| Seqloop : forall S T b c, sequential (@Cloop S T b c).
Hint Constructors sequential.


Lemma dec_comb : forall S T (c:circuit S T), combinatorial c \/ ~combinatorial c.
Proof.
introv; induction c as [?|?| ? ? ? ? IH1 ? IH2 | ? ? ? ? ? IH1 ? IH2 | ? ? ? ? IH].
- left. constructor.
- left. constructor.
- destruct IH1; destruct IH2.
  + left. constructor; easy.
  + right. intro N. Inverts N. false.
  + right. intro N. Inverts N. false.
  + right. intro N. Inverts N. false.
- destruct IH1; destruct IH2.
  + left. constructor; easy.
  + right. intro N. Inverts N. false.
  + right. intro N. Inverts N. false.
  + right. intro N. Inverts N. false.
- right. intro N. Inverts N. 
Qed.

Lemma plug_imp_comb : forall S T (c:circuit S T), wiring c -> combinatorial c.
Proof. introv H. induction H; easy. Qed.

Lemma not_comb_seq : forall S T U (c1:circuit S T) (c2:circuit T U), 
                     ~ combinatorial (c1) -o- (c2) -> ~ combinatorial c1 \/ ~ combinatorial c2.
Proof.
introv H. 
set (X1:= dec_comb c1). set (X2:= dec_comb c2). 
destruct X1; destruct X2; easy.
Qed.

Lemma not_comb_par : forall S T U V (c1:circuit S T) (c2:circuit U V), 
                     ~ combinatorial (-|c1,c2|-) -> ~ combinatorial c1 \/ ~ combinatorial c2.
Proof.
introv H. 
set (X1:= dec_comb c1). set (X2:= dec_comb c2). 
destruct X1; destruct X2; easy.
Qed.

Lemma seq_eq_notcomb : forall S T (c:circuit S T), sequential c <-> ~combinatorial c.
Proof.
split; introv H.
- induction H; introv C; Inverts C; false.
- induction c.
  + false; apply H. easy. 
  + false; apply H. easy. 
  + apply not_comb_seq in H. destruct H as [H|H]. 
    * apply IHc1 in H. apply Seqseql; easy.
    * apply IHc2 in H. apply Seqseqr; easy.
  +  apply not_comb_par in H. destruct H as [H|H]. 
    * apply IHc1 in H. apply Seqparl. easy.
    * apply IHc2 in H. apply Seqparr; easy.
  + easy.
Qed.  
 
Inductive nofork_circuit : forall S T, circuit S T -> Prop :=
(*| NFC1 : forall S g, (g<>(@Fork S)) -> nofork_circuit (@Cgate S (S#S) g) *)
| NFC0 : nofork_circuit (NOT)
| NFC1 : nofork_circuit (AND)
| NFC2 : nofork_circuit (OR)
| NFC3 : forall S, nofork_circuit (Cplug (Pid S))
| NFC4 : forall S T, nofork_circuit (Cplug (Swap S T))
| NFC5 : forall S T U, nofork_circuit (Cplug (Lsh S T U))
| NFC6 : forall S T U, nofork_circuit (Cplug (Rsh S T U))
| NFC7 : forall S T U c1 c2, nofork_circuit c1 -> nofork_circuit c2 -> nofork_circuit (@Cseq S T U c1 c2)
| NFC8 : forall S T U V c1 c2, 
         nofork_circuit c1 -> nofork_circuit c2 -> nofork_circuit (@Cpar S T U V c1 c2)
| NFC9 : forall S T c b, 
         nofork_circuit c -> nofork_circuit (@Cloop S T b c).
Hint Constructors nofork_circuit.


(** **           Some useful subcircuits                *)

(**                     Plugs                           *)

(** shuffle : ((a,b),(c,d)) -> ((a,c),(b,d))  *)
Definition shuffle a b c d : circuit ((a#b)#(c#d)) ((a#c)#(b#d))
           := LSH-o--|ID,SWAP|--o--|ID,LSH|--o-RSH-o--|ID,SWAP|-.

(** DUPL : (a,b) -> ((a,b),b)                 *)
Definition DUPL a b : circuit (a#b) ((a#b)#b)
           :=-|ID,FORK|- -o- RSH.

(** DIST : ((a,b),c) -> ((a,c),(b,c))         *)
Definition DIST a b c : circuit ((a#b)#c) ((a#c)#(b#c))
           :=-|ID,FORK|- -o- LSH-o--|ID,RSH -o- SWAP|--o- RSH.

(** SWAP_LR : ((a,b),c) -> ((a,c),b)          *)
Definition SWAP_LR a b c : circuit ((a#b)#c) ((a#c)#b)
           :=LSH-o--|ID,SWAP|--o-RSH.

(** SWAP_LS : ((a,b),c) -> (a,(c,b))          *)
Definition SWAP_LS a b c : circuit ((a#b)#c) (a#(c#b))
           :=LSH-o--|ID,SWAP|-.

(** SWAP_RL : (a,(b,c)) -> (b,(a,c))          *)
Definition SWAP_RL a b c : circuit (a#(b#c)) (b#(a#c))
           :=RSH-o--|SWAP,ID|--o-LSH.

(** SWAP32 : (a,(b,c)) -> (c,(b,a))          *)
Definition SWAP32 a b c : circuit (a#(b#c)) (c#(b#a))
           :=RSH-o--|SWAP,ID|--o-SWAP.


(** Cicuits emmiting constant values (without glitches)  *)
Definition Out0 : circuit § §
           := FORK -o--|NOT,ID|--o-AND.
Definition Out1 : circuit § §
           := FORK -o--|NOT,ID|--o-OR.

(**      Multiplexer 2 to 1                              *)
(* Mux21 select XO X1 = X0 if select = 0
                      = X1 if select = 1                 *)
Definition Mux21: circuit (§#(§#§)) § 
           :=  -|FORK,ID|--o-RSH-o--|LSH-o-SWAP,ID|--o-LSH-o--|-|NOT,ID|--o-AND,AND|--o-OR.

(** Simple sequentialy-organised memory cell  *)
Definition Celb (b:bool): circuit § § := -{b}-SWAP. 

(** Memory cells initialized to false or true *)
Definition Celf : circuit § § := -{false}-SWAP.
Definition Celt : circuit § § := -{true}-SWAP.

(** Memory cell with enable signal: (data, enable)out- if enable=1 then re-write *)
Definition CelbE (b:bool): circuit (§ # §) § 
           := -{b}-(-|SWAP,FORK|--o-RSH-o-SWAP-o--|ID,LSH-o--|ID,SWAP|--o-Mux21|-). 

(** Comparator:: 1 when not equal      *)
Definition eqG: circuit (§ # §) § 
           := -|FORK,FORK|--o-(shuffle § § § §)-o--|AND,-|NOT,NOT|--o-AND|--o-OR-o-NOT.

(* XOR : equivalent to eqG *)
Definition XOR: circuit (§ # §) § 
           := -|FORK,FORK|--o-(shuffle § § § §)-o--|OR,AND-o-NOT|--o-AND.

(** Majority voter for 3 inputs *)
Definition Voter31 : circuit ((§#§)#§) §
           := -|FORK,FORK|--o-LSH-o- -|AND,LSH|-
              -o--|ID, -|ID,RSH|- |- -o- -|ID, -|ID,SWAP|- |-
              -o--|ID,RSH|- -o--|ID, -|AND,AND|- |-
              -o--|ID,OR|--o-OR.

(** Triplicated majority voters 3-1  *)
Definition Tvoter31 : circuit  ((§#§)#§) ((§#§)#§) 
           := FORK -o--|FORK-o--|Voter31,Voter31|-,Voter31|-.

