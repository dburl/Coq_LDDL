
(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        Signals and Buses   
#</h1>#    
-   Types, conversions and basic properties 
#</center> <hr>#                                           *)
(*          Pascal Fradet - 2014_2015                      *)
(* ------------------------------------------------------- *)

Require Export Utils Equality Eqdep_dec.

Set Implicit Arguments.

(* ******************************************************* *)
(** *           Signals with glitches (SETs)               *)
(* ******************************************************* *)

Inductive sset : Set :=
| Zero   : sset
| One    : sset
| Glitch : sset.

Notation "0" := Zero.
Notation "1" := One.
Notation "?" := Glitch.

Definition eq_sset : forall x y : sset, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition beq_sset (s1 s2:sset) : bool :=
match (s1,s2) with
| (Zero, Zero)     => true
| (One, One)       => true
| (Glitch, Glitch) => true
| (_, _)           => false
end.

Lemma beq_sset_refl : forall s, beq_sset s s = true.
Proof. destruct s; easy. Qed.

Lemma beq_sset_true_iff : forall x y, beq_sset x y = true <-> x=y.
Proof. destruct x; destruct y; split; intro H; try inversion H; easy. Qed.



Lemma beq_sset_false_iff : forall x y, beq_sset x y = false <-> x<>y.
Proof. 
destruct x; destruct y; split; introv H1; try intro H2; 
try inversion H1; try inversion H2; try easy; try false.
Qed.


Inductive pure_sig : sset -> Prop := 
| Pure_sig0 : pure_sig 0
| Pure_sig1 : pure_sig 1. 

(** **           Conversion between bool and sset            *)

Inductive sig_bool : sset -> bool -> Prop := 
| Sigb0 : sig_bool 0 false
| Sigb1 : sig_bool 1 true.

Definition bool2sset (b:bool) : sset :=
match b with
| true  => One
| false => Zero
end.


(* ******************************************************* *)
(** * Type of buses (nested tuples of ssets or booleans    *)
(* ******************************************************* *)

Inductive bus : Set := 
| Wire : bus
| Pbus : bus -> bus -> bus.

Notation "x # y" := (Pbus x y)  (at level 60) : type_scope.
Notation "§"     := Wire : type_scope.


Lemma eqdec_bus : forall (t t':bus), {t = t'} + {t <> t'}.
Proof. decide equality. Defined.

Inductive eq_bus : bus -> bus -> Prop :=
| CTsig : eq_bus § §
| CPsig : forall S1 S2 T1 T2, eq_bus S1 T1 -> eq_bus S2 T2 -> eq_bus (S1#S2) (T1#T2).

(** An inversion getting rid of dependent equalities (on buses) without axioms *)

Ltac minvert_tactic H i1 i2 i3 i4 i5 i6 :=
  let rec go i1 i2 i3 i4 i5 i6 :=
    match goal with 
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh in intro H; 
                           first [ subst x | subst y ]; 
                           go i1 i2 i3 i4 i5 i6
     | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) 
           => match type of p with
              | bus =>   let H := fresh in intro H; 
                       generalize (@inj_pair2_eq_dec _ eqdec_bus P p x y H);
                       clear H; go i1 i2 i3 i4 i5 i6
              | _   => idtac
              end
    | |- (?P -> ?Q) => i1; go i2 i3 i4 i5 i6 ltac:(intro)
    | |- (forall _, _) => intro; go i1 i2 i3 i4 i5 i6
    end in
  generalize ltac_mark; invert keep H; go i1 i2 i3 i4 i5 i6;
  unfold eq' in *.

(** [minvert H] is same to [minvert keep H] except that it 
    clears hypothesis [H]. *)

Tactic Notation "minvert" "keep" hyp(H) :=
  minvert_tactic H ltac:(intro) ltac:(intro) ltac:(intro) 
                   ltac:(intro) ltac:(intro) ltac:(intro).

Tactic Notation "Inverts" hyp(H) :=
  minvert keep H; clear H.

Tactic Notation "Inverts_tactic" hyp(H) tactic(tac) :=
  let H' := fresh in rename H into H'; tac H'; clear H'.
Tactic Notation "Inverts" hyp(H) "as" simple_intropattern(I1) :=
 Inverts_tactic H (fun H => minvert_tactic H ltac:(intros I1) ltac:(intro)
                            ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro)).
Tactic Notation "Inverts" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) :=
 Inverts_tactic H (fun H => minvert_tactic H ltac:(intros I1) ltac:(intros I2)
                            ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro)).
Tactic Notation "Inverts" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) :=
 Inverts_tactic H (fun H => minvert_tactic H ltac:(intros I1) ltac:(intros I2)
                            ltac:(intros I3) ltac:(intro) ltac:(intro) ltac:(intro)).
Tactic Notation "Inverts" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
 Inverts_tactic H (fun H =>  minvert_tactic H ltac:(intros I1) ltac:(intros I2)
                            ltac:(intros I3) ltac:(intros I4) ltac:(intro) ltac:(intro)).
Tactic Notation "Inverts" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) 
 simple_intropattern(I5) :=
 Inverts_tactic H (fun H => minvert_tactic H ltac:(intros I1) ltac:(intros I2)
                            ltac:(intros I3) ltac:(intros I4) ltac:(intros I5) ltac:(intro)).
Tactic Notation "Inverts" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) 
 simple_intropattern(I5) simple_intropattern(I6) :=
 Inverts_tactic H (fun H => minvert_tactic H ltac:(intros I1) ltac:(intros I2)
                            ltac:(intros I3) ltac:(intros I4) ltac:(intros I5) ltac:(intros I6)).


(* depth_bus used to prove forall S T, S <> T#S and S <> S#T *)
(* I guess it could it be proved more directly !             *)
Fixpoint depth_bus (S:bus) : nat :=
match S with
| § => O
| S1 # S2 => 1+ (depth_bus S1) + (depth_bus S2)
end.

Lemma S_diff_T_S : forall (S T:bus), S <> T#S.
Proof.
introv H.
assert (X:depth_bus S = depth_bus (T#S)) by (rewrite <-H; easy). 
cbn in X. apply succ_plus_discr in X. exact X.
Qed.

Lemma S_diff_S_T : forall (S T:bus), S <> S#T.
Proof.
introv H.
assert (X:depth_bus S = depth_bus (S#T)) by (rewrite <-H; easy).
cbn in X. rewrite plus_comm in X. 
apply succ_plus_discr in X. exact X.
Qed.


(* ******************************************************* *)
(** *            Buses of pure signals (booleans)          *)
(* ******************************************************* *)

Inductive busig : bus -> Set :=
| Sig : bool -> busig §
| Psig: forall (S T:bus), busig S -> busig T -> busig (S#T).

Notation "[| x |]" := (busig x) : type_scope. 

Notation "[ x , y , .. , z ]" := (Psig .. (Psig x y) .. z): core_scope.
Notation "^ x" := (Sig x) (at level 80).

(** A dependent destruction for busig which does not require JMeq axiom *)

(* the general case for destruction of a buset variable *)

Lemma busig_case :
  forall X (P : [|X|] -> Type),
    (forall x (pf : Wire=X), P (eq_rect Wire _ (Sig x) X pf)) -> 
    (forall S T x y (pf : Pbus S T=X), P (eq_rect (Pbus S T) _ (Psig x y) X pf)) ->
    (forall x, P x).
Proof.
intros.
destruct x.
- specialize (X0 b eq_refl).
  rewrite <- Eqdep_dec.eq_rect_eq_dec in X0 by exact eqdec_bus.
  easy.
- specialize (X1 S T x1 x2 eq_refl).
  rewrite <- Eqdep_dec.eq_rect_eq_dec in X1 by exact eqdec_bus.
  easy.
Qed.

(* special case : Wire *)
Lemma busig_wire :
  forall (P : [|§|] -> Type),
    (forall x, P (Sig x)) -> 
    (forall x, P x).
Proof. 
intros.
apply busig_case; intros. 
- rewrite <- Eqdep_dec.eq_rect_eq_dec by exact eqdec_bus.
  apply X.
- Inverts pf.
Qed.

(* special case : Pair of buses *)
Lemma busig_tup : forall S T (P : [|S#T|] -> Type),
                    (forall x y, P (Psig x y) ) ->
                    (forall x, P x).
Proof.
intros.
apply busig_case; intros. 
- Inverts pf.
- dupl pf Z. Inverts pf. 
  rewrite <- Eqdep_dec.eq_rect_eq_dec by exact eqdec_bus.
  apply X.
Qed.

Ltac case_busig v :=
match type of v with
| [|§|]   => apply busig_wire
| [|_#_|] => apply busig_tup
| _       => apply busig_case; intros; subst; 
             rewrite <- Eqdep_dec.eq_rect_eq_dec by exact eqdec_bus
end.

Ltac ddestruct_b_base v :=  
            repeat  match goal with
                    | H : context[v] |- _ => revert H
                    end;    
                    pattern v; case_busig v; clear v.


Tactic Notation "Destruct_b" hyp(v) :=
   ddestruct_b_base v; intros.
Tactic Notation "Destruct_b" hyp(v) "as" simple_intropattern(I1) :=
  ddestruct_b_base v; intro I1; intros.
Tactic Notation "Destruct_b" hyp(v) "as" simple_intropattern(I1) simple_intropattern(I2) :=
  ddestruct_b_base v; intro I1; intro I2; intros.


(**    Boolean equality of busigs  *)

Fixpoint beq_busig_t (S:bus) : [|S|] -> [|S|] -> bool.
intros s t. destruct S; Inverts s; Inverts t. 
exact (eqb H H0).
exact  ((beq_busig_t S1 H1 H3) && (beq_busig_t S2 H2 H4)).
Defined.

Lemma eqdec_busig S (s t: [|S|]) : sumbool (s = t) (s <> t). (* {s=t} + {s<>t} %type *)
Proof.
induction s; Destruct_b t. 
       destruct b; destruct x; try easy;
       right; intro H; Inverts H.
       destruct (IHs1 x); destruct (IHs2 y);
       try (right; intro H; Inverts H; apply n; easy).
       subst. left. easy.
Defined.

(** Boolean equality implies equality *)
Lemma beq_busig_imp_eq : forall S (x y:[|S|]), beq_busig_t x y=true -> x=y.
Proof.
induction S; introv H.
- Destruct_b x as b; Destruct_b y as b0. 
  destruct b; destruct b0; try easy; Inverts H.
- Destruct_b x; Destruct_b y.
  Inverts H. apply andb_prop in H1. destruct H1 as [H1 H2].
  apply IHS1 in H1. apply IHS2 in H2. subst. easy.
Qed.

Lemma beq_busig_reflx : forall S (s:[|S|]), beq_busig_t s s = true.
Proof.
induction S; introv.
- Destruct_b s as b. 
  destruct b; try easy; Inverts H.
- Destruct_b s as s1 s2. 
  cbn. rewrite (IHS1 s1). rewrite (IHS2 s2). easy.
Qed.


Definition bool2bsig (b:bool) : [|§|] := ^b.

Definition bsig2bool (s: [|§|]) : bool:= 
match s with ^b => b end.

(* ******************************************************* *)
(** *       Buses of signals with SETs (glitches)          *)
(* ******************************************************* *)

Inductive buset : bus -> Set :=
| Sset : sset -> buset §
| Pset : forall S T, buset S -> buset T -> buset (S#T).

Notation "{| x |}" := (buset x) : type_scope. 
Notation "{ x , y , .. , z }" := (Pset .. (Pset x y) .. z) : core_scope.
Notation "~ x" := (Sset x).

(** A dependent destruction for buset which does not require JMeq axiom *)

(* the general case for destruction of a buset variable *)

Lemma buset_case :
  forall X (P : {|X|} -> Type),
    (forall x (pf : Wire=X), P (eq_rect Wire _ (Sset x) X pf)) -> 
    (forall S T x y (pf : Pbus S T=X), P (eq_rect (Pbus S T) _ (Pset x y) X pf)) ->
    (forall x, P x).
Proof.
intros.
destruct x.
- specialize (X0 s eq_refl).
  rewrite <- Eqdep_dec.eq_rect_eq_dec in X0 by exact eqdec_bus.
  easy.
- specialize (X1 S T x1 x2 eq_refl).
  rewrite <- Eqdep_dec.eq_rect_eq_dec in X1 by exact eqdec_bus.
  easy.
Qed.

(* special case : Wire *)
Lemma buset_wire :
  forall (P : {|§|} -> Type),
    (forall x, P (Sset x)) -> 
    (forall x, P x).
Proof. 
intros.
apply buset_case; intros. 
- rewrite <- Eqdep_dec.eq_rect_eq_dec by exact eqdec_bus.
  apply X.
- Inverts pf.
Qed.

(* special case : Pair of buses *)
Lemma buset_tup : forall S T (P : {|S#T|} -> Type),
                    (forall x y, P (Pset x y) ) ->
                    (forall x, P x).
Proof.
intros.
apply buset_case; intros. 
- Inverts pf.
- dupl pf Z. Inverts pf. 
  rewrite <- Eqdep_dec.eq_rect_eq_dec by exact eqdec_bus.
  apply X.
Qed.

Ltac case_buset v :=
match type of v with
| {|§|}   => apply buset_wire
| {|_#_|} => apply buset_tup
| _       => apply buset_case; intros; subst; 
             rewrite <- Eqdep_dec.eq_rect_eq_dec by exact eqdec_bus
end.

Ltac ddestruct_s_base v :=  
            repeat  match goal with
                    | H : context[v] |- _ => revert H
                    end;    
                    pattern v; case_buset v; clear v.


Tactic Notation "Destruct_s" hyp(v) :=
   ddestruct_s_base v; intros.
Tactic Notation "Destruct_s" hyp(v) "as" simple_intropattern(I1) :=
  ddestruct_s_base v; intro I1; intros.
Tactic Notation "Destruct_s" hyp(v) "as" simple_intropattern(I1) simple_intropattern(I2) :=
  ddestruct_s_base v; intro I1; intro I2; intros.

(**    Boolean equality of busets  *)

Fixpoint beq_buset_t (S:bus) : {|S|} -> {|S|} -> bool.
intros s t. destruct S; Inverts s; Inverts t. 
exact (beq_sset H H0).
exact  ((beq_buset_t S1 H1 H3) && (beq_buset_t S2 H2 H4)).
Defined.


Lemma beq_buset_reflx : forall S (s:{|S|}), beq_buset_t s s = true.
Proof.
induction S; introv.
- Destruct_s s as s.
  destruct s; try easy; Inverts H.
- Destruct_s s as s1 s2.
  cbn. rewrite (IHS1 s1). rewrite (IHS2 s2). easy.
Qed.

Lemma eq_imp_beq_buset : forall S (x y:{|S|}), x=y -> beq_buset_t x y=true.
Proof. introv H. subst. apply beq_buset_reflx.  Qed.

(** Boolean equality implies equality *)
Lemma beq_buset_imp_eq : forall S (x y:{|S|}), beq_buset_t x y=true -> x=y.
Proof.
induction S; introv H.
- Destruct_s x as x.  Destruct_s y as y.
  destruct x; destruct y; try easy; Inverts H.
- Destruct_s x.  Destruct_s y. 
  Inverts H. apply andb_prop in H1. destruct H1 as [H1 H2].
  apply IHS1 in H1. apply IHS2 in H2. subst. easy.
Qed.


(* Equivalence of bool and Prop difference of busets *)

Lemma diff_equiv_diff_buset : forall S (x y:{|S|}), x<>y <-> beq_buset_t x y=false.
Proof.
split; introv X. 
- apply not_true_is_false. introv Y.
  apply beq_buset_imp_eq in Y.
  false.
- intro Y. subst. 
  rewrite beq_buset_reflx in X.
  false. 
Qed. 

(* Equality of composed busets is equivalent of the equaliy of sub-components *)

Lemma dec_beq_buset : forall S T (x1 x2:{|S|}) (y1 y2:{|T|}),
                      beq_buset_t {x1,y1} {x2,y2} = andb (beq_buset_t x1 x2) (beq_buset_t y1 y2).
Proof. intros. cbn. easy. Qed.

(** Decidability of equality of busets    *)

Lemma eqdec_buset S (s t: {|S|}) : sumbool (s = t) (s <> t). (* {s=t} + {s<>t} %type *)
Proof.
induction s.
- Destruct_s t as t. 
  destruct s; destruct t; try easy;
  right; intro H; Inverts H.
- Destruct_s t as t1 t2.
  destruct (IHs1 t1); destruct (IHs2 t2);
  try (right; intro H; Inverts H; apply n; easy).
  subst. left. easy.
Defined.

(** ** Equality of buset modulo glitches                 *)
(** e.g., [1,[0,?]] eq_mod_G [?,[0,1]]                    *)
Inductive eq_mod_G  : forall (S:bus), {|S|} -> {|S|} -> Prop :=
| Emg1 : forall b:{|§|}, eq_mod_G b b
| Emg2 : forall b:{|§|}, eq_mod_G (~?) b
| Emg3 : forall b:{|§|}, eq_mod_G b (~?)
| Emg4 : forall S T s1 s2 t1 t2, @eq_mod_G S s1 t1 -> @eq_mod_G T s2 t2 -> eq_mod_G {s1,s2} {t1,t2}.
Hint Constructors eq_mod_G.

Lemma eq_mod_G_refl : forall S s, @eq_mod_G S s s.
Proof. introv. induction s; easy. Qed.

Lemma eq_mod_G_symm : forall S s t, @eq_mod_G S s t -> @eq_mod_G S t s.
Proof. introv H. induction s; Inverts H; easy. Qed.


(** **    pure_bset x if x doesn't contain glitches        *)

Inductive pure_bset : forall (S:bus), {|S|} -> Prop :=
| Pure_bset0 : pure_bset (~0)
| Pure_bset1 : pure_bset (~1)
| Pure_bsetp : forall S T s t, @pure_bset S s 
                            -> @pure_bset T t 
                            -> @pure_bset (S#T) {s,t}.
Hint Constructors pure_bset.

Fixpoint is_pure_bset (S:bus) (s:{|S|}) : bool := 
match s with
| ~0 => true
| ~1 => true
| {s1,s2} => (is_pure_bset s1) && (is_pure_bset s2)
| _ => false
end.

Lemma is_pure_equiv : forall S (s:{|S|}), pure_bset s <-> is_pure_bset s = true.
Proof.
split; introv H.
- induction H; try easy.
  apply andb_true_intro; split; easy.
- induction s.
  + destruct s; try easy.
    Inverts H.
  + Inverts H. 
    apply andb_prop in H1. destruct H1. 
    easy.
Qed.

(**           Functional version                *)

Fixpoint fpure_bset S (s:{|S|}) : bool :=
match s with
| (~0) => true
| (~1) => true
| (~?) => false
| {s1,s2} =>  fpure_bset s1 &&  fpure_bset s2
end.

Lemma fpure_bset_equiv : forall S (s:{|S|}), pure_bset s <-> fpure_bset s = true.
Proof.
split; introv H.
- induction s.
  + destruct s; try easy. Inverts H.
  + Inverts H. apply IHs1 in H3. apply IHs2 in H5.
    cbn. rewrite H3. rewrite H5. easy.
- induction s.
  + destruct s; try easy. Inverts H.
  + Inverts H.  apply andb_true_iff in H1.
    destruct H1 as [H3 H5].
    apply IHs1 in H3. apply IHs2 in H5.
    easy.
Qed.

(** **  Conversions between a buset wire and bool          *)

Definition bool2bset (b:bool) : {|§|} := ~(bool2sset b).


Lemma bool2bset_eq : forall b1 b2, bool2bset b1 = bool2bset b2 -> b1 = b2.
Proof.
introv H. destruct b1; destruct b2; Inverts H; easy.
Qed.

Inductive bset2bool : {|§|} -> bool -> Prop := 
| Ts2b_1 : bset2bool (~1) true
| Ts2b_0 : bset2bool (~0) false
| Ts2b_gt: bset2bool (~?) true
| Ts2b_gf: bset2bool (~?) false.
Hint Constructors bset2bool.


Lemma b2t_is_pure : forall b, pure_bset (bool2bset b).
Proof. introv. destruct b; cbv; easy. Qed.

Lemma pure_imp_exbool : forall (s:{|§|}), pure_bset s -> exists b, bool2bset b = s.
Proof. introv H.
Destruct_s s; destruct x.
- exists false. easy.
- exists true. easy.
- Inverts H.
Qed.


Lemma det_bset2bool : forall s b b', 
                      pure_bset s -> bset2bool s b -> bset2bool s b' -> b = b'.
Proof.
introv H1 H2 H3. Destruct_s s as s.
destruct s; destruct b; Inverts H2; Inverts H3; try easy.
Inverts H1. Inverts H1.
Qed.

Lemma s2bob2s : forall b1 b2, bset2bool (bool2bset b1) b2 <-> b1=b2.
Proof.
intros.
split; introv H; destruct b1; destruct b2; Inverts H; easy.
Qed.

Lemma fact_s2bob2s : forall b, bset2bool (bool2bset b) b.
Proof. intros. apply s2bob2s. reflexivity. Qed.

(** Functional definition of bset2bool (assumes that the argument is pure) *)
Definition fbset2bool (x:{|§|}) : bool:= 
match x with 
| (~1) => true
|  _   => false
end.

Lemma fbset2bool_equiv : forall a b, pure_bset a -> (bset2bool a b <-> fbset2bool a = b).
Proof.
introv P.
split; intro H; 
Destruct_s a; destruct x; destruct b; 
try Inverts P; try Inverts H; easy.
Qed.

Lemma b2bs_equiv_fb2bs : forall s:{|§|}, pure_bset s -> bool2bset (fbset2bool s) = s.
Proof.
introv P.
Destruct_s s; destruct x; Inverts P; reflexivity.
Qed.

Lemma rew_fbset2bool : forall b, fbset2bool (bool2bset b) = b.
Proof.
introv. apply fbset2bool_equiv.
- apply b2t_is_pure.
- apply s2bob2s. easy.
Qed.

Lemma rew_bool2bsetf: forall s, pure_bset s -> bool2bset (fbset2bool s) = s.
Proof. introv H. Destruct_s s; destruct x; try Inverts H; easy. Qed.


Inductive bset2bsig: forall (S:bus), {|S|} -> [|S|] -> Prop :=
| bs2bs_1 : bset2bsig (~1) (^true)
| bs2bs_0 : bset2bsig (~0) (^false)
| bs2bs_gt: bset2bsig (~?) (^true)
| bs2bs_gf: bset2bsig (~?) (^false)
| bs2bs_p : forall S T s1 s2 b1 b2, @bset2bsig S s1 b1
                                 -> @bset2bsig T s2 b2 
                                 -> @bset2bsig (S#T) {s1,s2} [b1,b2].
Hint Constructors bset2bsig. 


Lemma ex_bsig : forall S (s:{|S|}), exists b, bset2bsig s b.
Proof.
introv. induction S.
- Destruct_s s as s. destruct s.
  exists (^false). easy.
  exists (^true). easy.
  exists (^false). easy.
- Destruct_s s as s1 s2.
  destruct (IHS1 s1) as [b1 H1].
  destruct (IHS2 s2) as [b2 H2].
  exists [b1,b2]. easy.
Qed. 


Lemma det_bset2bsig : forall S (s:{|S|}) b b', 
                      pure_bset s -> bset2bsig s b -> bset2bsig s b' -> b = b'.
Proof.
introv H1 H2 H3. induction s. 
- destruct s;
  Inverts H1; Inverts H2; Inverts H3; try easy.
- Inverts H1. Inverts H2. Inverts H3.
  apply IHs1 with (b:=b1) (b':=b0) in H5; try easy.
  apply IHs2 with (b:=b2) (b':=b3) in H9; try easy.
  subst. easy.
Qed.

Fixpoint bsig2bset (S:bus) (b:[|S|]) : {|S|} :=
match b with
| ^true => ~1
| ^false => ~0
| [b1,b2] => {bsig2bset b1,bsig2bset b2}
end.

(**       Prop of being a pure stream                   *)
CoInductive pureStream : forall S, Stream {|S|} -> Prop :=
| P_Stream : forall S (Pi:{|S|}) Pis, pure_bset Pi -> pureStream Pis -> pureStream (Cons Pi Pis).

(** *           Tuples with glitches               *)

(* introglitch s s' iff  signals of s' have the    *)
(* same value as s except possibly for one         *)
(* which is remplaced by a Glitch                  *)
Inductive introglitch : forall (S:bus), {|S|} -> {|S|} -> Prop :=
| Tsin0 : introglitch (~0) (~?)
| Tsin1 : introglitch (~1) (~?)
| Tpinl : forall S T s s' t, @introglitch S s s'
                          -> @introglitch (S#T) {s,t} {s',t}
| Tpinr : forall S T s t t', @introglitch T t t'
                          -> @introglitch (S#T) {s,t} {s,t'}
| Tid   : forall S s, @introglitch S s s.
Hint Constructors introglitch.
(*
Lemma ig_eq_false : forall S (s:{|S|}), ~(introglitch s s).
Proof.
induction s; introv H.
- Inverts H.
- Inverts H. 
  + apply IHs1. easy. 
  + apply IHs2. easy.
Qed.

Lemma ig_imp_notpure : forall S s s', @introglitch S s s' -> ~pure_bset s'.
Proof. introv H. induction H; intro H1; Inverts H1; contradiction. Qed.
*)

(** **     tuples with exactly one glitch        *)
Inductive ex1glitch : forall S, {|S|} -> Prop :=
| Og_1 : ex1glitch (~?)
| Og_2 : forall S T s t, @ex1glitch S s -> @pure_bset T t -> ex1glitch {s,t}
| Og_3 : forall S T s t, @pure_bset S s -> @ex1glitch T t ->  ex1glitch {s,t}.
Hint Constructors ex1glitch.

(** **    tuples with at most one glitch *)
Inductive atmost1glitch : forall S, {|S|} -> Prop :=
| Am1g_1 : forall (s:{|§|}), atmost1glitch s
| Am1g_2 : forall S T s t, @atmost1glitch S s -> @pure_bset T t -> atmost1glitch {s,t}
| Am1g_3 : forall S T s t, @pure_bset S s -> @atmost1glitch T t ->  atmost1glitch {s,t}.
Hint Constructors atmost1glitch.
(*
Lemma intro_imp_ex1g : forall S s s', pure_bset s -> @introglitch S s s' -> ex1glitch s'.
Proof. introv H I. induction I; Inverts H; try easy. Qed.


Lemma intro_imp_neg_tsitb : forall S s s', @introglitch S s s' -> ~pure_bset s'.
Proof. introv I T. induction I; try (Inverts T); easy. Qed.
*)

Lemma ex1_imp_atmost1 : forall S s, @ex1glitch S s -> atmost1glitch s.
Proof.
introv H. induction s.
- constructor.
- Inverts H; easy.
Qed.

Lemma intro_imp_atmost1 : forall S s s', pure_bset s -> @introglitch S s s' -> atmost1glitch s'.
Proof. introv H I. induction s.
- easy.
- inverts I; inverts H. 
  + apply IHs1 in H1; try easy. 
  + apply IHs2 in H1; try easy. 
  + assert (X:introglitch s1 s1) by constructor. 
    apply IHs1 in X; try easy. 
Qed.

Lemma pure_imp_atmost1 : forall S s, @pure_bset S s -> atmost1glitch s.
Proof.
introv H. induction s.
- constructor.
- Inverts H; easy.
Qed.


Lemma emG_pure : forall S (a b:{|S|}), pure_bset a -> pure_bset b -> eq_mod_G a b -> a=b.
Proof. 
introv T1 T2 H. induction H.
- easy.
- Inverts T1.
- Inverts T2.
- Inverts T1. Inverts T2.
  apply IHeq_mod_G1 in H5; try easy.
  apply IHeq_mod_G2 in H8; try easy.
  subst. easy.
Qed. 


(** **  Primitive operations on busigs        *)

Definition negB (x:[|§|]) :=
match x with
| (^b) => ^(negb b)
end.
Arguments negB !x /.

Definition andB (x : [|§#§|]) :=
match x with
| @Psig Wire Wire (^true) (^true) => (^true)
| @Psig Wire Wire _ _             => (^false)
end.
Arguments andB !x /.


Definition orB (x : [|§#§|]) :=
match x with
| @Psig Wire Wire (^false) (^false) => (^false)
| @Psig Wire Wire _ _               => (^true)
end.
Arguments orB !x /.

Definition fstB (A B : bus) (p: [|A#B|]) := match p with [a,b] => a end.

Definition sndB (A B : bus) (p: [|A#B|]) := match p with [a,b] => b end.

Definition pidB (S:bus) (s:[|S|]) := s.

Definition forkB  (S:bus) (s:[|S|]) := [s,s].

Definition swapB (S T:bus) (s:[|S#T|]) := [sndB s,fstB s].

Definition lshB (S T U:bus) (s:[|(S#T)#U|])
           := [fstB (fstB s), [sndB (fstB s),sndB s]].

Definition rshB (S T U:bus) (s:[|S#(T#U)|])
           := [[fstB s, fstB (sndB s)],sndB (sndB s)].


(** **  Primitive operations on busets        *)

Definition negS (x:{|§|}) :=
match x with
| ~0 => ~1
| ~1 => ~0
| ~? => ~?
end.
Arguments negS !x /.

Lemma pure_negS : forall s, pure_bset s -> pure_bset (negS s).
Proof.
introv P.
Destruct_s s; destruct x; try Inverts P; easy.
Qed.

Definition andS (x : {|§#§|}) :=
match x with
| @Pset Wire Wire (~0) y    => (~0)
| @Pset Wire Wire x (~0)    => (~0)
| @Pset Wire Wire (~1) (~1) => (~1)
| @Pset Wire Wire _ _       => (~?)
end.
Arguments andS !x /.

Lemma pure_andS : forall s, pure_bset s -> pure_bset (andS s).
Proof.
introv P.
Destruct_s s. Inverts P.
Destruct_s x; destruct x; try Inverts H2; 
Destruct_s y; destruct x; try Inverts H4; easy.
Qed.

Definition orS (x : {|§#§|}) :=
match x with
| @Pset Wire Wire (~1) y    => (~1)
| @Pset Wire Wire x (~1)    => (~1)
| @Pset Wire Wire (~0) (~0) => (~0)
| @Pset Wire Wire _ _       => (~?)
end.
Arguments orS !x /.

Lemma pure_orS : forall s, pure_bset s -> pure_bset (orS s).
Proof.
introv P.
Destruct_s s. Inverts P.
Destruct_s x; destruct x; try Inverts H2; 
Destruct_s y; destruct x; try Inverts H4; easy.
Qed.


Definition fstS (A B : bus) (p: {|A#B|}) := match p with {a,b} => a end.

Definition sndS (A B : bus) (p: {|A#B|}) := match p with {a,b} => b end.

Definition pidS (S:bus) (s:{|S|}) := s.

Definition forkS  (S:bus) (s:{|S|}) := {s,s}.

Definition swapS (S T:bus) (s:{|S#T|}) := {sndS s,fstS s}.

Definition lshS (S T U:bus) (s:{|(S#T)#U|})
           := {fstS (fstS s), {sndS (fstS s),sndS s}}.

Definition rshS (S T U:bus) (s:{|S#(T#U)|})
           := {{fstS s, fstS (sndS s)},sndS (sndS s)}.

