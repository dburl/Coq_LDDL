 
(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        Checking properties on circuits by reflection        
#</h1>#    
#</center> <hr>#                                           *)
(*          Pascal Fradet - 2014_2015                      *)
(* ------------------------------------------------------- *)

Require Export PropSub.

Set Implicit Arguments.

Section MakeSet. 

Variable A:Set.
Variable eqdec_A : forall x y : A, sumbool (x = y) (x <> y).
Variable beq_A : A-> A -> bool.
Hypothesis beq_A_eq : forall a b, beq_A a b = true <-> a=b.


(** Checking if a result already occurs in a list of results   *)
Fixpoint mem (a:A) l : bool :=
match l with
| nil => false
| a1 :: xl => if (beq_A a a1) then true else mem a xl
end.

Lemma mem_equiv_in : forall (l:list A) (x:A), mem x l = true <-> In x l.
Proof.
split. 
- induction l; introv H.
  + Inverts H.
  + destruct (eqdec_A x a).
    * subst. easy.
    * cbn in H.
      cases (beq_A x a) as G.
      { apply beq_A_eq in G. false. } 
      { apply IHl in H. easy. }
- induction l; introv H.
  + Inverts H.
  + destruct (eqdec_A x a).
    * subst. unfold mem. 
      assert (X:beq_A a a =true) by (apply beq_A_eq; easy).
      rewrite X. easy.
    * cbn. destruct (beq_A x a). easy.
      cbn in H. destruct H. false.
      apply IHl in H. easy.     
Qed.


(** Suppressing duplicates in a list of results   *)

Definition mkset (l:list A) : list A 
          := fold_right (fun b l => if mem b l then l else b::l) nil l.


Lemma mkset_correct : forall (l:list A) (x:A), In x l <-> In x (mkset l).
Proof.
split; induction l; introv H; Simpl.
- destruct (eqdec_A x a).
  + subst. destruct (in_dec (eqdec_A) a l) as [F|F].
    * apply IHl in F; try easy. simpl.
      destruct (mem a (mkset l)); easy.
    * simpl. cases (mem a (mkset l)) as G.
      apply mem_equiv_in. easy. easy.
  + cbn in H. destruct H. false.
    apply IHl in H; try easy. simpl.
    destruct (mem a (mkset l)); easy.
- simpl in H. destruct (eqdec_A x a).
  + easy. 
  + destruct (mem a (mkset l)). easy.
    apply in_inv in H. destruct H; easy.
Qed.

(** Checks that Qb holds for all results in the list                                   *)
Definition ForAll_Q A (Qb: A -> bool) (l:list A) : bool
           := fold_left andb (List.map Qb l) true.


Lemma fact_Andb : forall l i, fold_left andb l i = true -> i=true.
Proof.
induction l; introv H; cbn in H.
- easy.
- apply IHl in H. 
  apply andb_true_iff in H.
  destruct H. easy. 
Qed.

Lemma fact2_Andb : forall l x i, fold_left andb l i = true -> In x l -> x=true.
Proof.
induction l; introv H I; cbn in H.
- Inverts I.
- apply in_inv in I. destruct I as [I|I].
  + apply  fact_Andb in H. apply andb_true_iff in H. 
    destruct H. subst. easy.
  + eapply IHl in H; try exact I. easy. 
Qed.


Lemma ForAll_Q_safe : forall (x:A)  l Qb, 
                    In x l -> ForAll_Q Qb l = true -> Qb x=true.
Proof.
induction l; introv I H.
- Inverts I. 
- unfold ForAll_Q in H.
  cbn in H. dupl H H1. apply fact_Andb in H1. rewrite H1 in H.
  destruct (eqdec_A x a).
  + subst. easy.
  + cbn in I. destruct I as [I|I]; try solve[false].
    apply IHl in H; easy.
Qed.

End MakeSet. 


(**   Functional version of introglitch                                    *)
(** takes a buset s and produces the list of possible busets after an SET  *)

Fixpoint fintroglitch1 (S:bus) (s:{|S|}) : list {|S|} :=
match s with
| ~x => (~?)::nil
| {s1,s2} => List.map (fun x1 => {x1,s2}) (fintroglitch1 s1) ++ List.map (fun x2 => {s1,x2}) (fintroglitch1 s2) 
end.

Definition fintroglitch (S:bus) (s:{|S|}) := s::(fintroglitch1 s).

Lemma fintroglitch_equiv : forall S (s s':{|S|}),
                           pure_bset s -> (introglitch s s' <-> In s' (fintroglitch s)).
Proof.
introv P. split; introv H.
- induction H; try easy; Inverts P. 
  + dupl H3 X. 
    apply IHintroglitch in H3.
    destruct H3.
    * subst. apply in_eq. 
    * apply in_cons. cbn. apply in_or_app. 
      left. apply in_map_iff.
      exists s'. easy. 
  + dupl H5 X. 
    apply IHintroglitch in H5.
    destruct H5.
    * subst. apply in_eq. 
    * apply in_cons. cbn. apply in_or_app. 
      right. apply in_map_iff.
      exists t'. easy.
- induction s; cbn in H.
  + destruct H as [H|H].
    * subst. easy.
    * destruct H as [H|H]. subst. destruct s; constructor. Inverts H.
  + Inverts P. destruct H as [H|H]; try (subst; easy).
    apply in_app_or in H. destruct H as [H|H].
    * apply in_map_iff in H. destruct H as [s'1 [? H]]. subst.
      apply IHs1 with (s':=s'1) in H3; try exact H. easy.
      apply in_cons. easy.
    * apply in_map_iff in H. destruct H as [s'2 [? H]]. subst.
      apply IHs2 with (s':=s'2) in H5; try exact H. easy.
      apply in_cons. easy.
Qed.


(** *    Functional semantics of circuits                                *)
(**     produces a set of possible circuits if glitches reaches cells     *)

Fixpoint fsteps S T (c: circuit S T): {|S|} -> ({|T|} * list (circuit S T)):=
if is_comb c then fun x => (redcomb c x, c::nil) else
match c with
| Cgate g     => fun x => (redgate g x, Cgate g ::nil)

| Cplug p     => fun x => (redplug p x, Cplug p ::nil)

| Cseq c1 c2  => fun x => let (t1,c1s) := fsteps c1 x in
                          let (t2,c2s) := fsteps c2 t1 in
                          (t2, List.map (fun c => (fst c) -o- (snd c))(list_prod c1s c2s))

| Cpar c1 c2 => fun x => let (t1,c1s) := fsteps c1 (fstS x) in
                         let (t2,c2s) := fsteps c2 (sndS x) in
                         ({t1,t2}, List.map (fun c => -|fst c, snd c|-)(list_prod c1s c2s))

| Cloop b c  => fun x => let (t1,c1s) := fsteps c {x,bool2bset b} in
                         match (sndS t1) with
                         | ~0 => (fstS t1,List.map (fun c' => -{false}-c') c1s)
                         | ~1 => (fstS t1,List.map (fun c' => -{true}-c') c1s) 
                         | ~? => (fstS t1,(List.map (fun c' => -{false}-c') c1s) ++
                                          (List.map (fun c' => -{true}-c') c1s))
                         end
end.


Lemma fsteps_comb_safe : forall S T (c : circuit S T) s t,
                         combinatorial c -> (step c s t c <-> fsteps c s = (t, c::nil)).
Proof.
introv C. 
dupl C C1. apply comb_equiv_is_comb in C.
split; intro H1.
- apply redcomb_equiv_step in H1; try easy. subst.
  destruct c; cbn; Inverts C; try rewrite H0; try easy.
- eapply redcomb_equiv_step; try easy.
  destruct c; cbn in H1; Inverts H1; try easy.
  + Inverts C. rewrite H1 in H0; Inverts H0; easy.
  + Inverts C. rewrite H1 in H0; Inverts H0; easy.
  + Inverts C1.
Qed.


Lemma fsteps_safe : forall S T (c c': circuit S T) s t,
                    step c s t c' <-> t=fst (fsteps c s) /\ In c' (snd (fsteps c s)).
Proof.
intros. split. 
- induction c; introv H; Inverts H; try easy.
  + dupl H4 H3. dupl H9 H5.
    apply IHc1 in H3. destruct H3 as [H3 H2].
    apply IHc2 in H5. destruct H5 as [H5 H6].
    cases (is_comb c1 -o- c2) as C1; Inverts C1; cbn; rewrite H0.
    * apply andb_true_iff in H0. destruct H0 as [C1 C2].
      apply comb_equiv_is_comb in C1. dupl C1 C3.
      eapply step_comb_cir in C3; try exact H4. rewrite <- C3.
      eapply step_imp_redcomb in H4; try easy.
      apply comb_equiv_is_comb in C2. dupl C2 C4.
      eapply step_comb_cir in C4; try exact H9. rewrite <- C4.
      eapply step_imp_redcomb in H9; try easy.
      rewrite <- H9. rewrite <- H4. easy.
    * destruct (fsteps c1 s). subst. cbn in *.
      destruct (fsteps c2 b). cbn in *.
      assert (Z:In (c1',c2') (list_prod l l0)) by (apply in_prod_iff; easy).
      apply in_map with (f:=fun c => (fst c) -o- (snd c)) in Z. easy.
  + dupl H3 H4. dupl H10 H5.
    apply IHc1 in H3. destruct H3 as [H2 H3].
    apply IHc2 in H5. destruct H5 as [H5 H6].
    cases (is_comb (-| c1, c2 |-)) as C1; Inverts C1; cbn; rewrite H0.
    * apply andb_true_iff in H0. destruct H0 as [C1 C2].
      apply comb_equiv_is_comb in C1. dupl C1 C3.
      eapply step_comb_cir in C3; try exact H4. rewrite <- C3.
      eapply step_imp_redcomb in H4; try easy.
      apply comb_equiv_is_comb in C2. dupl C2 C4.
      eapply step_comb_cir in C4; try exact H10. rewrite <- C4.
      eapply step_imp_redcomb in H10; try easy.
      rewrite <- H10. rewrite <- H4. easy.
    * cbn. destruct (fsteps c1 s0). cbn in *. subst.
      destruct (fsteps c2 u). cbn in *. split. easy.
      assert (Z:In (c1',c2') (list_prod l l0)) by (apply in_prod_iff; easy).
      apply in_map with (f:=fun x => Cpar (fst x) (snd x)) in Z.
      easy.
  + apply IHc in H8. destruct H8 as [H1 H2]. cbn.
    destruct (fsteps c {s, bool2bset b}). Dd_buset b0. Inverts H1. cbn. 
    Destruct_s x0. destruct x0; cbn; split; try easy; Inverts H7.
    * apply in_map with (f:=fun x => (-{false}- x)). easy.
    * apply in_map with (f:=fun x => (-{true}- x)). easy.
    * apply in_or_app. right. apply in_map with (f:=fun x => (-{true}- x)). easy.
    * apply in_or_app. left. apply in_map with (f:=fun x => (-{false}- x)). easy.
- induction c; introv H; cbn in H; destruct H as [H H1].
  + destruct H1 as [H1 | H1]; Inverts H1. easy.
  + destruct H1 as [H1 | H1]; Inverts H1. easy.
  + cases (is_comb c1 -o- c2) as C1; Inverts C1; cbn; 
    rewrite H2 in H; rewrite H2 in H1; cbn in *; subst. 
    * destruct H1 as [H1|H1]; Inverts H1. 
      eapply redcomb_imp_step; try easy. 
      apply comb_equiv_is_comb. easy.
    * assert (X1 :  exists t1, exists lc1,  (t1,lc1)= fsteps c1 s)
      by (exists (fst (fsteps c1 s)) (snd (fsteps c1 s)); destruct (fsteps c1 s); easy).
      destruct X1 as [t1 [lc1 X1]]. rewrite <- X1 in H1. 
      assert (X2 :  exists t2, exists lc2,  (t2,lc2)= fsteps c2 t1)
      by (exists (fst (fsteps c2 t1)) (snd (fsteps c2 t1)); destruct (fsteps c2 t1); easy).
      destruct X2 as [t2 [lc2 X2]]. rewrite <- X2 in H1.
      cbn in *. apply in_map_iff in H1.
      destruct H1 as [x [E I]]. 
      destruct x. apply in_prod_iff in I. destruct I as [I1 I2].
      cbn in E. subst.
      assert (XI1: t1 = fst (fsteps c1 s) /\ In c (snd (fsteps c1 s)))
      by (rewrite <- X1; easy).
      assert (XI2: t2 = fst (fsteps c2 t1) /\ In c0 (snd (fsteps c2 t1)))
      by (rewrite <- X2; easy). rewrite <- X1. rewrite <- X2. cbn.
      apply IHc1 in XI1. apply IHc2 in XI2.
      apply Sseq with (t:=t1); easy.
  + cases (is_comb (-|c1,c2|-)) as C1; Inverts C1; cbn; 
    rewrite H2 in H; rewrite H2 in H1; cbn in *; subst. 
    * destruct H1 as [H1|H1]; Inverts H1. 
      eapply redcomb_imp_step; try easy. 
      apply comb_equiv_is_comb. easy.
    * Dd_buset s. cbn in *.
      assert (X1 :  exists t1, exists lc1,  (t1,lc1)= fsteps c1 x)
      by (exists (fst (fsteps c1 x)) (snd (fsteps c1 x)); destruct (fsteps c1 x); easy).
      destruct X1 as [t1 [lc1 X1]]. rewrite <- X1 in H1. 
      assert (X2 :  exists t2, exists lc2,  (t2,lc2)= fsteps c2 x0)
      by (exists (fst (fsteps c2 x0)) (snd (fsteps c2 x0)); destruct (fsteps c2 x0); easy).
      destruct X2 as [t2 [lc2 X2]]. rewrite <- X2 in H1.
      rewrite <- X1.  rewrite <- X2. cbn in *. 
      apply in_map_iff in H1.
      destruct H1 as [y [E I]]. 
      destruct y. apply in_prod_iff in I. destruct I as [I1 I2].
      cbn in E. subst.
      assert (XI1: t1 = fst (fsteps c1 x) /\ In c (snd (fsteps c1 x)))
      by (rewrite <- X1; easy).
      assert (XI2: t2 = fst (fsteps c2 x0) /\ In c0 (snd (fsteps c2 x0)))
      by (rewrite <- X2; easy).
      apply IHc1 in XI1. apply IHc2 in XI2.
      easy. 
  + assert (X :  exists t, exists lc,  (t,lc)= fsteps c {s, bool2bset b})
    by (exists (fst (fsteps c {s, bool2bset b})) (snd (fsteps c {s, bool2bset b} )); 
         destruct (fsteps c {s, bool2bset b} ); easy).
    destruct X as [t1 [lc X]]. rewrite <- X in H. rewrite <- X in H1. 
    Dd_buset t1. 
    Destruct_s x0. destruct x0; cbn in*.
    * apply in_map_iff in H1. destruct H1 as [c1 [C I]].
      assert (XI: {x, ~ 0} = fst (fsteps c {s, bool2bset b})
               /\ In c1 (snd (fsteps c {s, bool2bset b})))
      by (rewrite <- X; easy). 
      subst. apply Sloop with (a:=~0); easy. 
    * apply in_map_iff in H1. destruct H1 as [c1 [C I]].
      assert (XI: {x, ~ 1} = fst (fsteps c {s, bool2bset b})
               /\ In c1 (snd (fsteps c {s, bool2bset b})))
      by (rewrite <- X; easy). 
      subst. apply Sloop with (a:=~1); easy.
    * apply in_app_iff in H1. destruct H1 as [H1 | H1];
        apply in_map_iff in H1; destruct H1 as [c1 [C I]];  
        assert (XI: {x, ~ ?} = fst (fsteps c {s, bool2bset b})
               /\ In c1 (snd (fsteps c {s, bool2bset b})))
        by (rewrite <- X; easy); 
        subst; apply Sloop with (a:=~?); easy.
Qed.

Definition fstepls S T (c: circuit S T): {|S|} -> list ({|T|} * (circuit S T)):=
fun s => List.map (fun c' => (fst (fsteps c s),c')) (snd (fsteps c s)).

Lemma fstepls_safe : forall S T (c c': circuit S T) s t,
                    step c s t c' <-> In (t,c') (fstepls c s).
Proof.
split; introv H.
- unfold fstepls.
  apply (in_map_iff (fun c': circuit S T => (fst (fsteps c s), c'))).
  exists c'. apply fsteps_safe in H. destruct H.  
  subst. easy.
- unfold fstepls in H.
  apply (in_map_iff (fun c': circuit S T => (fst (fsteps c s), c'))) in H.
  destruct H as [x [H1 H2]]. Inverts H1.
  apply fsteps_safe. easy.
Qed. 


(** *    Functional semantics of circuits with an SET occurrence         *)
(*     produces the set of possible (result,circuit)                     *)

Fixpoint fstepgs S T (c: circuit S T): {|S|} -> list ({|T|} * (circuit S T)):=
if is_wiring c then fun x => (redcomb c x, c)::nil else
match c with
| Cgate g   => fun x => List.map (fun x => (x, Cgate g)) (fintroglitch (redgate g x))
| Cplug p   => fun x => (redplug p x, Cplug p)::nil
| Cseq c1 c2
  => fun x => let (t1,c1s) := fsteps c1 x in
              let  tc2s1   := List.map (fun c => (fst(snd c),(fst c) -o- (snd (snd c))))
                               (list_prod c1s (fstepgs c2 t1)) in
              let  tc1s    := fstepgs c1 x in
              let  tc2s2   := List.flat_map (fun x => let (t2s,c2s) := fsteps c2 (fst x) in
                                             List.map (fun c2' => (t2s,(snd x) -o- c2')) c2s) tc1s in
              tc2s1 ++ tc2s2
(* suppressing the duplicates here can gain a lot (but safety proof should be revised) 
   i.e. mkset (@mycomp s u) (tc2s1 ++ tc2s2) 
   with Definition mycomp S T (x y:{|T|} * (circuit S T)) :=
                   andb (beq_buset_t (fst x) (fst y)) (beq_circuit (snd x) (snd y)).
*)
| Cpar c1 c2 
  => fun x => let (t1,c1s) := fsteps c1 (fstS x)  in
              let (t2,c2s) := fsteps c2 (sndS x)  in
              let  tc1s    := fstepgs c1 (fstS x) in
              let  tc2s    := fstepgs c2 (sndS x) in
                  (List.map (fun c => ({t1,fst(snd c)},-|fst c,snd (snd c)|-)) (list_prod c1s tc2s))
               ++ (List.map (fun c => ({fst(fst c),t2},-|snd (fst c),snd c|-)) (list_prod tc1s c2s))


| Cloop b c
  => fun x => let tcs1 := fstepgs c {x,bool2bset b} in
              let (t2,c2s) := fsteps c {x,~?} in
              List.flat_map (fun tc => match (sndS (fst tc)) with
                                       | ~0 => (fstS (fst tc),-{false}-(snd tc))::nil
                                       | ~1 => (fstS (fst tc),-{true}-(snd tc))::nil
                                       | ~? => (fstS (fst tc),-{false}-(snd tc))::
                                               (fstS (fst tc),-{true}-(snd tc))::nil
                                       | _  => nil
                                       end) (tcs1 ++ (List.map (fun c => (t2,c)) c2s))
end.

Lemma fstepgs_wiring_safe : forall S T (c : circuit S T) s t,
                            wiring c -> (stepg c s t c <-> fstepgs c s = (t, c)::nil).
Proof.
introv C. 
dupl C C1.  apply wiring_equiv_is_wiring in C.
split; intro H1.
- apply wiring_equ_step_g in H1; try easy. subst.
  apply plug_imp_comb in C1.
  apply  fsteps_comb_safe in H1; try easy.
  destruct c; cbn; Inverts C.
  * Inverts H1; try easy.
  * rewrite H0. apply comb_equiv_is_comb in C1. Inverts C1.
    cbn in H1. rewrite H2 in H1. Inverts H1. easy.
  * rewrite H0. apply comb_equiv_is_comb in C1. Inverts C1.
    cbn in H1. rewrite H2 in H1. Inverts H1. easy.
- eapply wiring_equ_step_g; try easy.
  destruct c; cbn in H1; Inverts H1; Inverts C1; try easy.
  + Inverts C. rewrite H1 in H0. Inverts H0. 
    apply redcomb_imp_step; try easy. 
    constructor; apply plug_imp_comb; easy.
  + Inverts C. rewrite H1 in H0. Inverts H0. 
    apply redcomb_imp_step; try easy. 
    constructor; apply plug_imp_comb; easy.
Qed.

Lemma  step_in_fstepgs : forall S T (c c':circuit S T) s t, 
                         step c s t c' -> In (t,c') (fstepgs c s).

Proof. 
introv H. induction H; cbn; subst. 
- easy.
- easy.
- cases (is_wiring c1 && is_wiring c2) as C1; Inverts C1; try easy.
  + eapply andb_true_iff in H2. destruct H2 as [G1 G2].
    apply wiring_equiv_is_wiring in G1.
    apply wiring_equiv_is_wiring in G2.
    apply plug_imp_comb in G1. dupl G1 G3.
    apply plug_imp_comb in G2. dupl G2 G4.
    eapply step_comb_cir in G1; try exact H.
    eapply step_comb_cir in G2; try exact H0.
    eapply step_imp_redcomb in G3; try exact H.
    eapply step_imp_redcomb in G4; try exact H0.
    subst. easy.
  + destruct (fsteps c1 s) as [t' lc1] eqn:X1.
    destruct (fsteps c2 t') as [u' lc2] eqn:X2.
    apply in_or_app.
    left.
    apply in_map_iff.
    exists (c1',(u,c2')). cbn. split. easy. 
    apply in_prod_iff. 
    apply fsteps_safe in H. rewrite X1 in H.
    destruct H. subst. easy.
- cases (is_wiring c1 && is_wiring c2) as C1; Inverts C1; try easy.
  + eapply andb_true_iff in H2. destruct H2 as [G1 G2].
    apply wiring_equiv_is_wiring in G1.
    apply wiring_equiv_is_wiring in G2.
    apply plug_imp_comb in G1. dupl G1 G3.
    apply plug_imp_comb in G2. dupl G2 G4.
    eapply step_comb_cir in G1; try exact H.
    eapply step_comb_cir in G2; try exact H0.
    eapply step_imp_redcomb in G3; try exact H.
    eapply step_imp_redcomb in G4; try exact H0.
    subst. easy.
  + simpl fstS. simpl sndS.
    destruct (fsteps c1 s) as [t' lc1] eqn:X1.
    destruct (fsteps c2 u) as [v' lc2] eqn:X2.
    apply in_or_app.
    left.
    apply in_map_iff.
    apply fsteps_safe in H. rewrite X1 in H.
    apply fsteps_safe in H0. rewrite X2 in H0.
    destruct H. destruct H0. subst. 
    exists (c1',(v',c2')). cbn. split. easy. 
    apply in_prod_iff. easy.
- destruct (fsteps c {s, ~ ?} ) as [t1 lc] eqn:X1.
  apply in_flat_map.
  exists ({t, a}, c').
  split. apply in_or_app. easy.
  cbn. Destruct_s a; destruct x; Inverts H; easy.
Qed.

Lemma fstepgs_safe : forall S T (c c': circuit S T) s t,
                     pure_bset s -> (stepg c s t c' <-> In (t,c') (fstepgs c s)).
Proof.
introv P. split; introv H.
- induction H; cbn.
  + Inverts H.
    * right. apply in_map_iff. exists (~?). 
      split; try easy. 
      rewrite <- H0. easy.
    * right. apply in_map_iff. exists (~?). 
      split; try easy. 
      rewrite <- H0. easy.
    * Destruct_g g.
    * Destruct_g g. 
    * easy. 
  + subst. easy.
  + cases (is_wiring c1 -o- c2) as C1; Inverts C1; cbn; rewrite H2.
    * apply andb_true_iff in H2. destruct H2 as [C1 C2].
      apply wiring_equiv_is_wiring in C1. 
      apply wiring_equ_step_g in H; try easy.
      apply wiring_equiv_is_wiring in C2. 
      apply plug_imp_comb in C1. apply plug_imp_comb in C2.
      dupl C1 C3. dupl C2 C4.
      eapply step_comb_cir in C3; try exact H.
      eapply step_comb_cir in C4; try exact H0.
      apply step_imp_redcomb in H; try easy.
      apply step_imp_redcomb in H0; try easy.
      subst. easy.
    * apply IHstepg in P. destruct (fsteps c1 s).
      apply in_or_app. right.
      apply in_flat_map. exists (t,c1').
      split. easy. cbn.
      apply fsteps_safe in H0. destruct H0 as [H0 H1].
      destruct (fsteps c2 t). subst. cbn in *.
      apply in_map_iff.
      exists c2'. easy.
  + cases (is_wiring c1 -o- c2) as C1; Inverts C1; cbn; rewrite H2.
    * apply andb_true_iff in H2. destruct H2 as [C1 C2].
      apply wiring_equiv_is_wiring in C2. 
      apply wiring_equ_step_g in H0; try easy.
      apply wiring_equiv_is_wiring in C1. 
      apply plug_imp_comb in C1. apply plug_imp_comb in C2.
      dupl C1 C3. dupl C2 C4.
      eapply step_comb_cir in C3; try exact H.
      eapply step_comb_cir in C4; try exact H0.
      apply step_imp_redcomb in H; try easy.
      apply step_imp_redcomb in H0; try easy.
      subst. easy.
    * Purestep H. apply IHstepg in P0.
      apply fsteps_safe in H. destruct H as [H H1].
      destruct (fsteps c1 s).
      apply in_or_app. left.
      apply in_map_iff. exists (c1',(u,c2')). subst. cbn in *.
      split. easy.
      apply in_prod_iff. easy. 
  + cases (is_wiring (-|c1,c2|-))as C1; Inverts C1; cbn; rewrite H2.
     * apply andb_true_iff in H2. destruct H2 as [C1 C2].
      apply wiring_equiv_is_wiring in C1. 
      apply wiring_equ_step_g in H; try easy.
      apply wiring_equiv_is_wiring in C2. 
      apply plug_imp_comb in C1. apply plug_imp_comb in C2.
      dupl C1 C3. dupl C2 C4.
      eapply step_comb_cir in C3; try exact H.
      eapply step_comb_cir in C4; try exact H0.
      apply step_imp_redcomb in H; try easy.
      apply step_imp_redcomb in H0; try easy.
      subst. easy.
    * Inverts P. apply IHstepg in H5. 
      apply fsteps_safe in H0. destruct H0 as [H0 H1]. 
      cbn. destruct (fsteps c1 s). destruct (fsteps c2 u).
      apply in_or_app. right.
      apply in_map_iff. exists ((t,c1'),c2'). subst. cbn in *.
      split. easy. 
      apply in_prod_iff; easy. 
  + cases (is_wiring (-|c1,c2|-))as C1; Inverts C1; cbn; rewrite H2.
    * apply andb_true_iff in H2. destruct H2 as [C1 C2].
      apply wiring_equiv_is_wiring in C2. 
      apply wiring_equ_step_g in H0; try easy.
      apply wiring_equiv_is_wiring in C1. 
      apply plug_imp_comb in C1. apply plug_imp_comb in C2.
      dupl C1 C3. dupl C2 C4.
      eapply step_comb_cir in C3; try exact H.
      eapply step_comb_cir in C4; try exact H0.
      apply step_imp_redcomb in H; try easy.
      apply step_imp_redcomb in H0; try easy.
      subst. easy.
    * Inverts P. apply IHstepg in H7. 
      apply fsteps_safe in H. destruct H as [H H1]. 
      cbn. destruct (fsteps c1 s). destruct (fsteps c2 u).
      apply in_or_app. left.  
      apply in_map_iff. exists (c1',(v,c2')). subst. cbn in *.
      split. easy. 
      apply in_prod_iff; easy.
  + assert (X: pure_bset {s, bool2bset b}) by Checkpure.
    apply IHstepg in X.
    destruct (fsteps c {s, ~ ?}). 
    apply in_flat_map. exists ({t, a}, c').
    split. 
    * apply in_app_iff. left. easy.
    * Destruct_s a. destruct x; Inverts H; try easy.
  + assert (X:{t, a}= fst (fsteps c {s, bg}) /\ In c' (snd (fsteps c {s, bg})))
    by (apply fsteps_safe;easy).
    destruct X as [X1 X2].
    Inverts H. destruct (fsteps c {s, ~ ?}). cbn in *. Dd_buset b0.
    Inverts X1.
    apply in_flat_map. 
    exists ({x, x0}, c').
    split.
    * apply in_or_app. right. apply in_map_iff. exists c'. easy.
    * cbn. Destruct_s x0. destruct x; Inverts H0; try easy.
    * destruct (fsteps c {s, ~ ?}). cbn in *. Dd_buset b0.
      Inverts X1. apply in_flat_map. 
      exists ({x,x0}, c'). split.
      apply in_or_app. right. apply in_map_iff. exists c'. easy.
      cbn. Destruct_s x0. destruct x; Inverts H0; try easy.
    * destruct (fsteps c {s, ~ ?}) eqn:X. 
      cbn in *. apply in_flat_map.
      exists ({t,a},c'). split. 
      apply in_or_app. left. rewrite X1.
      eapply  step_in_fstepgs. rewrite <- X1. easy.
      cbn. Purestep H1. Inverts P0. Inverts H0; try easy.
- induction c; cbn in H.
  + destruct H as [H|H].
    * Inverts H. constructor. constructor. 
    * apply in_map_iff in H. 
      destruct H as [x [H H1]].
      Inverts H.
      constructor. apply fintroglitch_equiv; try easy.
      eapply redgate_pure. exact P. easy.
  + destruct H as [H|H]. Inverts H. constructor. easy. false. 
  + cases (is_wiring c1 -o- c2)as C1; Inverts C1; 
    cbn; rewrite H1 in H; cbn in *; subst.
    * apply andb_true_iff in H1.   
      destruct H1 as [C1 C2].
      apply wiring_equiv_is_wiring in C1. 
      apply wiring_equiv_is_wiring in C2.
      apply wiring_equ_step_g; try (constructor; easy). 
      apply plug_imp_comb in C1. apply plug_imp_comb in C2. 
      Inverts H; Inverts H0.
      eapply redcomb_imp_step; try easy.
    * clear H1.
      assert (X1 :  exists t1, exists lc1,  (t1,lc1)= fsteps c1 s)
      by (exists (fst (fsteps c1 s)) (snd (fsteps c1 s)); 
      destruct (fsteps c1 s); easy). destruct X1 as [t1 [lc1 X1]].
      rewrite <- X1 in H.
      apply in_app_or in H. destruct H as [H|H].
        apply in_map_iff in H. destruct H as [x [H H1]].
        destruct x as [d1 [x d2]]. Inverts H.
        apply in_prod_iff in H1. destruct H1 as [H1 H2].
        assert (X2: t1=fst (fsteps c1 s) /\ In d1 (snd (fsteps c1 s)))
        by (rewrite <- X1; easy).
        eapply fsteps_safe in X2. Purestep X2.
        eapply Sseqg2 with (t:=t1); easy.
    
        clear X1. apply in_flat_map in H.
        destruct H as [x [H H1]]. destruct x as [t11 c11].
        assert (X1 :  exists t2, exists lc2,  (t2,lc2)= fsteps c2 t11)
        by (exists (fst (fsteps c2 t11)) (snd (fsteps c2 t11)); 
          destruct (fsteps c2 t11); easy). destruct X1 as [t2 [lc2 X1]].
        apply IHc1 in H; try easy.
        cbn in H1. rewrite <- X1 in H1.
        apply in_map_iff in H1. destruct H1 as [c12 [H1 H2]].
        Inverts H1.
        assert (X2: t=fst (fsteps c2 t11) /\ In c12 (snd (fsteps c2 t11)))
        by (rewrite <- X1; easy).
        eapply fsteps_safe in X2.
        eapply Sseqg1 with (t:=t11); easy.

  + cases (is_wiring (-|c1,c2|-)) as C1; Inverts C1; 
    cbn; rewrite H1 in H; cbn in *; subst.
    * apply andb_true_iff in H1.   
      destruct H1 as [C1 C2].
      apply wiring_equiv_is_wiring in C1. 
      apply wiring_equiv_is_wiring in C2.
      apply wiring_equ_step_g; try (constructor; easy). 
      apply plug_imp_comb in C1. apply plug_imp_comb in C2. 
      Inverts H; Inverts H0.
      eapply redcomb_imp_step; try easy.
    * clear H1.
      Dd_buset s. Inverts P. cbn in *.
      assert (X1 :  exists t1, exists lc1,  (t1,lc1)= fsteps c1 x)
      by (exists (fst (fsteps c1 x)) (snd (fsteps c1 x)); 
      destruct (fsteps c1 x); easy). destruct X1 as [t1 [lc1 X1]].
      assert (X2 :  exists t2, exists lc2,  (t2,lc2)= fsteps c2 x0)
      by (exists (fst (fsteps c2 x0)) (snd (fsteps c2 x0)); 
      destruct (fsteps c2 x0); easy). destruct X2 as [t2 [lc2 X2]].
      rewrite <- X1 in H. rewrite <- X2 in H.
      apply in_app_or in H. destruct H as [H|H].
        apply in_map_iff in H. destruct H as [y [H H1]].
        destruct y as [d1 [y d2]]. Inverts H.
        apply in_prod_iff in H1. destruct H1 as [H1 H2].
        assert (X3: t1=fst (fsteps c1 x) /\ In d1 (snd (fsteps c1 x)))
        by (rewrite <- X1; easy).
        eapply fsteps_safe in X3. Purestep X3.
        apply IHc2 in H2; try easy.
        eapply Sparg2 with (t:=t1); easy. 
    
        apply in_map_iff in H. destruct H as [y [H H1]].
        destruct y as [[y d1] d2]. Inverts H.
        apply in_prod_iff in H1. destruct H1 as [H1 H2].
        assert (X3: t2=fst (fsteps c2 x0) /\ In d2 (snd (fsteps c2 x0)))
        by (rewrite <- X2; easy).
        eapply fsteps_safe in X3. Purestep X3.
        apply IHc1 in H1; try easy.
        eapply Sparg1 with (t:=y); easy.   
  + assert (X: pure_bset {s, bool2bset b}) by Checkpure.
    assert (Y:exists tt ccs, (tt,ccs) = fsteps c {s, ~ ?})
    by (destruct (fsteps c {s,~?}); exists b0 l; easy).
    destruct Y as [tt [ccs Y]].
    rewrite <- Y in H.
    apply in_flat_map in H. destruct H as [x [H H1]].
    destruct x.
    Dd_buset b0.  cbn in *. Destruct_s x0. destruct x0;
    apply in_app_or in H; destruct H as [H|H]; Inverts H1; Inverts H0.
    * eapply IHc in X; try exact H.
      apply Sloopg1 with (a:=~0); easy.
    * apply in_map_iff in H. destruct H as [x [H I]].
      Inverts H.  apply Sloopg2 with (a:=~0) (bg:=~?); try easy.
      destruct b; easy. 
      apply fsteps_safe. rewrite <- Y. easy.
    * eapply IHc in X; try exact H.
      apply Sloopg1 with (a:=~1); easy.
    * apply in_map_iff in H. destruct H as [x [H I]].
      Inverts H.  apply Sloopg2 with (a:=~1) (bg:=~?); try easy.
      destruct b; easy. 
      apply fsteps_safe. rewrite <- Y. easy.
    * eapply IHc in X; try exact H.
      apply Sloopg1 with (a:=~?); easy.
    * eapply IHc in X; try exact H. Inverts H1.
      apply Sloopg1 with (a:=~?); easy.
    * Inverts H1.
    * apply in_map_iff in H. destruct H as [x [H I]].
      Inverts H.  apply Sloopg2 with (a:=~?) (bg:=~?); try easy.
      destruct b; easy. 
      apply fsteps_safe. rewrite <- Y. easy.
    * Inverts H1. 
      apply in_map_iff in H. destruct H as [x [H I]].
      Inverts H.  apply Sloopg2 with (a:=~?) (bg:=~?); try easy.
      destruct b; easy. 
      apply fsteps_safe. rewrite <- Y. easy.
    * Inverts H1.
Qed.

(** Optimized version (suppresses duplicates) *)

Definition beq_res_cir S T (x y:{|T|} * (circuit S T)) :=
                   andb (beq_buset_t (fst x) (fst y)) (beq_circuit (snd x) (snd y)).

Lemma eqdec_res_cir : forall S T (x y:{|T|} * (circuit S T)), sumbool (x = y) (x <> y).
Proof. 
decide equality. 
- apply eqdec_circuit.
- apply eqdec_buset.
Defined.

Lemma beq_res_cir_eq : forall S T (x y:{|T|} * (circuit S T)), beq_res_cir  x y = true <-> x=y.
Proof.
split; introv H.
- apply andb_true_iff in H. destruct H as [H H1].
  apply beq_circuit_imp_eq in H1.
  apply beq_buset_imp_eq in H.
  destruct x. destruct y. cbn in *. subst. reflexivity.
- subst. unfold beq_res_cir. rewrite beq_buset_reflx. 
  rewrite beq_circuit_reflx. easy.
Qed.

Fixpoint fstepgo S T (c: circuit S T): {|S|} -> list ({|T|} * (circuit S T)):=
if is_wiring c then fun x => (redcomb c x, c)::nil else
match c with
| Cgate g   => fun x =>  List.map (fun x => (x, Cgate g)) (fintroglitch (redgate g x))
| Cplug p   => fun x => (redplug p x, Cplug p)::nil
| @Cseq s t u c1 c2
  => fun x => let (t1,c1s) := fsteps c1 x in
              let  tc2s1   := List.map (fun c => (fst(snd c),(fst c) -o- (snd (snd c))))
                               (list_prod c1s (fstepgo c2 t1)) in
              let  tc1s    := fstepgo c1 x in
              let  tc2s2   := List.flat_map (fun x => let (t2s,c2s) := fsteps c2 (fst x) in
                                             List.map (fun c2' => (t2s,(snd x) -o- c2')) c2s) tc1s in
              mkset (@beq_res_cir s u) (tc2s1 ++ tc2s2) 

| Cpar c1 c2
  => fun x => let (t1,c1s) := fsteps c1 (fstS x)  in
              let (t2,c2s) := fsteps c2 (sndS x)  in
              let  tc1s    := fstepgo c1 (fstS x) in
              let  tc2s    := fstepgo c2 (sndS x) in
                  (List.map (fun c => ({t1,fst(snd c)},-|fst c,snd (snd c)|-)) (list_prod c1s tc2s))
               ++ (List.map (fun c => ({fst(fst c),t2},-|snd (fst c),snd c|-)) (list_prod tc1s c2s))


| Cloop b c
  => fun x => let tcs1 := fstepgo c {x,bool2bset b} in
              let (t2,c2s) := fsteps c {x,~?} in
              List.flat_map (fun tc => match (sndS (fst tc)) with
                                       | ~0 => (fstS (fst tc),-{false}-(snd tc))::nil
                                       | ~1 => (fstS (fst tc),-{true}-(snd tc))::nil
                                       | ~? => (fstS (fst tc),-{false}-(snd tc))::
                                               (fstS (fst tc),-{true}-(snd tc))::nil
                                       | _  => nil
                                       end) (tcs1 ++ (List.map (fun c => (t2,c)) c2s))
end.

Lemma fstepgs_equiv_fstepgo : forall S T (c c':circuit S T) s t, 
                              In (t,c') (fstepgs c s) <-> In (t,c') (fstepgo c s).
Proof. 
split; introv H.
- induction c; Simpl; cbn in *.
  + cases (is_wiring c1 -o- c2) as C1; Inverts C1; 
    cbn; rewrite H1 in *; Simpl. 
    destruct (fsteps c1 s).
    apply mkset_correct; try apply eqdec_res_cir; try apply beq_res_cir_eq.
    apply in_or_app. apply in_app_or in H. destruct H as [H|H].
    * left. apply in_map_iff. apply in_map_iff in H.
      destruct H as [x [H2 H3]]. 
      exists x. split. easy. 
      destruct x. apply in_prod_iff. apply in_prod_iff in H3. 
      destruct H3 as [H3 H]. destruct p. apply IHc2 in H.
      easy.
    * right. apply in_flat_map. apply in_flat_map in H.
      destruct H as [x [H2 H3]]. 
      exists x. split; try easy. 
      destruct x. apply IHc1 in H2. easy.
  + cases (is_wiring  (-| c1, c2 |-)) as C1; Inverts C1; 
    cbn; rewrite H1 in *; Simpl. cbn. 
    destruct (fsteps c1 x1). destruct (fsteps c2 x2).
    apply in_or_app. apply in_app_or in H. destruct H as [H|H].
    * left. apply in_map_iff. apply in_map_iff in H.
      destruct H as [z [H2 H3]]. 
      exists z. split. easy. 
      destruct z. apply in_prod_iff. apply in_prod_iff in H3. 
      destruct H3 as [H3 H]. destruct p. apply IHc2 in H.
      easy.
    * right. eapply in_map_iff. apply in_map_iff in H.
      destruct H as [z [H2 H3]]. 
      exists z. split; try easy. 
      destruct z. apply in_prod_iff. apply in_prod_iff in H3. 
      destruct H3 as [H3 H]. destruct p. apply IHc1 in H3.
      easy.
  + destruct (fsteps c {s, ~ ?}).
    apply in_flat_map. apply in_flat_map in H.
    destruct H as [x [H H1]].
    exists x. apply in_app_or in H.
    destruct x. split; try apply in_or_app; destruct H; eauto.
- induction c; Simpl; cbn in *. 
  + cases (is_wiring c1 -o- c2) as C1; Inverts C1; 
    cbn; rewrite H1 in *; Simpl. 
    destruct (fsteps c1 s).
    apply mkset_correct in H; try apply eqdec_res_cir; try apply beq_res_cir_eq.
    apply in_or_app. apply in_app_or in H. destruct H as [H|H].
    * left. apply in_map_iff. apply in_map_iff in H.
      destruct H as [x [H2 H3]]. 
      exists x. split. easy. 
      destruct x. apply in_prod_iff. apply in_prod_iff in H3. 
      destruct H3 as [H3 H]. destruct p. apply IHc2 in H.
      easy.
    * right. apply in_flat_map. apply in_flat_map in H.
      destruct H as [x [H2 H3]]. 
      exists x. split; try easy. 
      destruct x. apply IHc1 in H2. easy.
  + cases (is_wiring  (-| c1, c2 |-)) as C1; Inverts C1; 
    cbn; rewrite H1 in *; Simpl. cbn. 
    destruct (fsteps c1 x1). destruct (fsteps c2 x2).
    apply in_or_app. apply in_app_or in H. destruct H as [H|H].
    * left. apply in_map_iff. apply in_map_iff in H.
      destruct H as [z [H2 H3]]. 
      exists z. split. easy. 
      destruct z. apply in_prod_iff. apply in_prod_iff in H3. 
      destruct H3 as [H3 H]. destruct p. apply IHc2 in H.
      easy.
    * right. eapply in_map_iff. apply in_map_iff in H.
      destruct H as [z [H2 H3]]. 
      exists z. split; try easy. 
      destruct z. apply in_prod_iff. apply in_prod_iff in H3. 
      destruct H3 as [H3 H]. destruct p. apply IHc1 in H3.
      easy.
  + destruct (fsteps c {s, ~ ?}).
    apply in_flat_map. apply in_flat_map in H.
    destruct H as [x [H H1]].
    exists x. apply in_app_or in H.
    destruct x. split; try apply in_or_app; destruct H; eauto.
Qed.

Lemma fstepgo_safe : forall S T (c c': circuit S T) s t,
                     pure_bset s -> (stepg c s t c' <-> In (t,c') (fstepgo c s)).
Proof.
introv P. split; introv H.
- apply fstepgs_equiv_fstepgo.
  apply fstepgs_safe; easy.
- apply fstepgs_safe; try easy.
  apply fstepgs_equiv_fstepgo. easy.
Qed.

(** Equivalence between a property and its boolean equivalent  *)
Definition prop_imp_bool (t:Set) (X:t->Prop) (Xb:t->bool) : Prop 
           := forall  (x:t), (X x) -> (Xb x = true).
Definition bool_imp_prop (t:Set) (Xb:t->bool) (X:t->Prop) : Prop 
           := forall  (x:t), (Xb x = true) -> (X x).
Definition eq_prop_bool (t:Set) (X:t->Prop) (Xb:t->bool)  : Prop 
           := forall  (x:t), (X x) <-> (Xb x = true).

(** Types of results and equality on them  *)

(* complete environment : parameters, output, circuit *)
Definition Env_ptc P S T := prod (prod {|P|} {|T|}) (circuit S T).



(** Boolean equality  of (p,t,c) type of environment *)
Definition beq_ptc P S T (e1 e2:Env_ptc P S T) : bool :=
   (beq_buset_t (fst (fst e1)) (fst (fst e2))) 
&& (beq_buset_t (snd (fst e1)) (snd (fst e2))) 
&& (beq_circuit (snd e1) (snd e2)).

(** Decidability of equality of results  *)
Definition eqdec_ptc P S T (e1 e2:Env_ptc P S T) : sumbool (e1 = e2) (e1 <> e2).
Proof.
destruct e1 as [e1 e13]; destruct e1 as [e11 e12];
destruct e2 as [e2 e23]; destruct e2 as [e21 e22].
destruct (eqdec_buset e11 e21); destruct (eqdec_buset e12 e22);
destruct (eqdec_circuit e13 e23);
subst; try (right; intro H; apply n; Inverts H; easy).
left; easy.
Defined.


Lemma eq_beq_ptc : forall P S T (e1 e2:Env_ptc P S T), beq_ptc e1 e2 = true <-> e1=e2.
Proof.
split; introv H.
- destruct e1 as [e1 e13]; destruct e1 as [e11 e12];
  destruct e2 as [e2 e23]; destruct e2 as [e21 e22].
  unfold beq_ptc in H. cbn in H.
  apply andb_prop in H. destruct H as [H H3].
  apply andb_prop in H. destruct H as [H1 H2].
  apply beq_buset_imp_eq in H1. 
  apply beq_buset_imp_eq in H2. 
  apply beq_circuit_imp_eq in H3.
  subst. easy.
- unfold beq_ptc. 
  destruct e1 as [e1 e13]; destruct e1 as [e11 e12];
  destruct e2 as [e2 e23]; destruct e2 as [e21 e22].
  Inverts H. cbn. 
  rewrite (beq_buset_reflx e21).
  rewrite (beq_buset_reflx e22).
  rewrite (beq_circuit_reflx e23). easy.
Qed.



(** Generates all possible sset buses of type S  *)
Fixpoint allS (S:bus) : list ({|S|}) :=
match S with
| § => cons (~1) (cons (~0) (cons (~?) nil))
| U#V => List.map (fun x => {fst x, snd x}) (list_prod (allS U) (allS V))
end.

Lemma fact_allS: forall S (s:{|S|}), In s (allS S).
Proof.
induction S; introv.
- Destruct_s s. destruct x; easy.
- Destruct_s s.
  assert (H1:In x (allS S1)) by (apply (IHS1 x)).
  assert (H2:In y (allS S2)) by (apply (IHS2 y)).
  eapply in_prod in H2; try exact H1.
  cbn.
  replace {x,y} with {fst (x,y),snd(x,y)}; try easy.
  apply (in_map  (fun x : {|S1|} * {|S2|} => {fst x, snd x})).
  easy.
Qed.

(** keeps only sset values that verify Pb    *)

Definition filterP (S:bus) (Pb : {|S|} -> bool)  := filter Pb (allS S).

Lemma P_in_filterP : forall S (s:{|S|}) P Pb, 
                     prop_imp_bool P Pb -> P s -> In s (filterP Pb).
Proof.
introv E H. unfold filterP. 
assert (X:In s (allS S)) by (apply fact_allS).
apply E in H.
apply filter_In; easy.
Qed.


(* ################################################################################### *)
(*                                   Reflection process                                *)
(* relative to a parameterized circuit (c p)                                           *)
(*             a parameterized input (I p)                                             *)
(*             a precondiction P (and Pb its boolean version)                          *)
(*             a postcondiction Q (and Qb its boolean version)                         *)
(* The computation checks for all buses s verifying Pb that Qb holds for all results   *)
(* (t,c) belonging to fstep(g)s (X x) (I y)                                            *)
(* The correctness Lemma ensures that we can conclude                                  *)
(*                       P(x,y) -> step(g) c s t c' -> Q(x,y,t,c')                     *)
(* ################################################################################### *)

(** * The computation reflecting : forall p t c, P p -> step (C p) (I p) t c -> Q(p,t,c) *)

Definition step_reflect_ptc P S T (C:{|P|} -> circuit S T) (I:{|P|} -> {|S|})
                                  (Pb : {|P|} -> bool) (Qb: Env_ptc P S T -> bool) : bool
           := ForAll_Q Qb (* (mkset (@beq_ptc P S T) *)
                          (flat_map (fun p => let (t,lc) :=fsteps (C p) (I p) in
                                              List.map (fun c=>(p,t,c)) lc)
                                    (filterP Pb)).


Lemma ptc_in_listfsteps : forall P S T p t (C:{|P|} -> circuit S T) 
                                           (I:{|P|} -> {|S|}) (c:circuit S T) l,
                          In p l -> step (C p) (I p) t c 
                       -> In (p,t,c) (flat_map (fun p => let (t,lc) :=fsteps (C p) (I p) in
                                                List.map (fun c=>(p,t,c)) lc) l).
Proof.
introv E H.
apply fsteps_safe in H; try easy.
destruct H as [H H1].
apply in_flat_map.
exists p. split. easy.
destruct (fsteps (C p) (I p)). 
eapply in_map_iff.
exists c. subst. easy.
Qed.


Lemma step_reflect_ptc_safe : forall P S T Pp Pb Qp Qb (C:{|P|} -> circuit S T) (I:{|P|} -> {|S|}),
                          prop_imp_bool Pp Pb
                       -> bool_imp_prop Qb Qp
                       -> step_reflect_ptc C I Pb Qb = true
                       -> (forall p t (c:circuit S T), Pp p -> step (C p) (I p) t c -> Qp(p,t,c)).
Proof.
introv EqP EqQ Cc Xp Xs.
unfold step_reflect_ptc in Cc.
eapply P_in_filterP with (P:=Pp) in EqP; try exact Xp.
apply ptc_in_listfsteps with (l:= filterP Pb) in Xs; try easy.
eapply ForAll_Q_safe  in Xs; try apply eqdec_ptc; try exact Cc.
apply EqQ. easy.
Qed.

(** * The computation reflecting : forall p t c, P p -> stepg (C p) (I p) t c -> Q(p,t,c) *)
Definition stepg_reflect_ptc P S T (C:{|P|} -> circuit S T) (I:{|P|} -> {|S|})
                                   (Pb : {|P|} -> bool) 
                                   (Qb: Env_ptc P S T -> bool) : bool
           := ForAll_Q Qb  (* (mkset (@beq_xstc X Y S T) *)
                          (flat_map (fun p => let ltc := fstepgs (C p) (I p) in
                                              List.map (fun tc => (p,fst tc,snd tc)) ltc)
                                    (filterP Pb)).

Lemma ptc_in_listfstepg : forall P S T p t (C:{|P|} -> circuit S T) 
                                                (I:{|P|} -> {|S|}) (c:circuit S T) l,
                           In p l -> pure_bset (I p) -> stepg (C p) (I p) t c 
                        -> In (p,t,c) (flat_map (fun p => let ltc := fstepgs (C p) (I p) in
                                                 List.map (fun tc => (p,fst tc,snd tc)) ltc) l).
Proof.
introv E U H.
apply fstepgs_safe in H; try easy.
apply in_flat_map.
exists p. split. easy.
cbn. apply in_map_iff. 
exists (t,c). easy.
Qed.


Definition imp_pure P S (Pp: {|P|} -> Prop) (I:{|P|} -> {|S|}) : Prop 
           := forall p , Pp p -> pure_bset (I p).

Lemma stepg_reflect_ptc_safe : forall P S T Pp Pb Qp Qb (C:{|P|} -> circuit S T) (I:{|P|} -> {|S|}),
                           prop_imp_bool Pp Pb
                        -> bool_imp_prop Qb Qp
                        -> imp_pure Pp I
                        -> stepg_reflect_ptc C I Pb Qb = true
                        -> (forall p t (c:circuit S T), Pp p -> stepg (C p) (I p) t c -> Qp(p,t,c)).
Proof.
introv EqP EqQ Pur Calc Xp Xs.
unfold stepg_reflect_ptc in Calc.
eapply P_in_filterP with (P:=Pp) in EqP; try exact Xp.
apply ptc_in_listfstepg with (l:= filterP Pb) in Xs; apply Pur in Xp; try easy.
eapply ForAll_Q_safe  in Xs; 
      try apply eqdec_ptc; try exact Calc.
apply EqQ. easy.
Qed.


(* "optimized" version *)
Definition stepg_reflo_ptc P S T (C:{|P|} -> circuit S T) (I:{|P|} -> {|S|})
                                   (Pb : {|P|} -> bool) 
                                   (Qb: Env_ptc P S T -> bool) : bool
           := ForAll_Q Qb  (* (mkset (@beq_xstc X Y S T) *)
                          (flat_map (fun p => let ltc := fstepgo (C p) (I p) in
                                              List.map (fun tc => (p,fst tc,snd tc)) ltc)
                                    (filterP Pb)).


Lemma ptc_in_listfstepgo : forall P S T p t (C:{|P|} -> circuit S T) 
                                                (I:{|P|} -> {|S|}) (c:circuit S T) l,
                           In p l -> pure_bset (I p) -> stepg (C p) (I p) t c 
                        -> In (p,t,c) (flat_map (fun p => let ltc := fstepgo (C p) (I p) in
                                                 List.map (fun tc => (p,fst tc,snd tc)) ltc) l).
Proof.
introv E U H.
apply fstepgo_safe in H; try easy.
apply in_flat_map.
exists p. split. easy.
cbn. apply in_map_iff. 
exists (t,c). easy.
Qed.

Lemma stepg_reflo_ptc_safe : forall P S T Pp Pb Qp Qb (C:{|P|} -> circuit S T) (I:{|P|} -> {|S|}),
                           prop_imp_bool Pp Pb
                        -> bool_imp_prop Qb Qp
                        -> imp_pure Pp I
                        -> stepg_reflo_ptc C I Pb Qb = true
                        -> (forall p t (c:circuit S T), Pp p -> stepg (C p) (I p) t c -> Qp(p,t,c)).
Proof.
introv EqP EqQ Pur Calc Xp Xs.
unfold stepg_reflo_ptc in Calc.
eapply P_in_filterP with (P:=Pp) in EqP; try exact Xp.
apply ptc_in_listfstepgo with (l:= filterP Pb) in Xs; apply Pur in Xp; try easy.
eapply ForAll_Q_safe  in Xs; 
      try apply eqdec_ptc; try exact Calc.
apply EqQ. easy.
Qed.

(**        Tactics making the Reflection step more automatic          *)
(** Requires properties to be in the following specific form :        *)
(** forall p t c, ((fun p => P) p)                                    *)
(**            -> step(g) ((fun p => C p) p) ((fun p=> I) p) t c      *)
(**            -> (fun e => Q) (p,t,c).                               *)
(** p represents the parameters of the properties gathered in a buset *)
(** t represents the result of the circuit c                          *)
(** The pre-condition is expressed relatively to p                    *)
(** The reduction step is done on parameterized circuits and inputs   *)
(** The post-condition Q is expressed relatively to p,t and c         *) 
(** gathered in a tuple e.                                            *)  

Ltac tautowithEx :=
match goal with 
| [ |- exists (_:bool), _ ] =>  (exists true; tautowithEx) || (exists false; tautowithEx)
| [ |- exists (_:{|§|}),_ ] =>  (exists (~1); tautowithEx) || (exists (~0); tautowithEx) 
                                || (exists (~?); tautowithEx)
| _ => tauto
end.

Ltac BoolimpProp1 := 
(repeat match goal with 
| [H: andb _ _ = _ |- _]           => apply andb_true_iff in H; destruct H
| [H: orb _ _ = _ |- _]            => apply orb_true_iff in H; destruct H
| [H: beq_buset_t _ _ =  _ |- _]   => apply beq_buset_imp_eq in H

| [H: (_ : circuit _ _) = _  |- _ ] => apply beq_circuit_imp_eq in H 
end); subst.

Ltac BoolimpProp H := revert_all_but H; BoolimpProp1; intros; try tautowithEx.


Ltac PropimpBool1 := 
(repeat match goal with 
| [H: _ /\ _ |- _] => destruct H 
| [H: _ \/ _ |- _] => destruct H
| [H: pure_bset _ |- _] => apply fpure_bset_equiv in H
end); subst; vm_compute; easy.

Ltac PropimpBool H := revert_all_but H; cbn in H; PropimpBool1; intros.

(* Tactic to transform pre- and post-conditions as Prop in their boolean form   *)
(* It accepts /\, \/, not, equality between busets or circuits, pure_bset and   *)
(* (non-nested ?) exists.                                                       *)

Ltac Refl P :=
match eval cbn in P with
| (fun x => @?X x = @?Y x) => match (type of X) with
                             | _ -> bool        => constr:(fun x => eqb (X x) (Y x))
                             | _ -> buset _     => constr:(fun x => beq_buset_t  (X x)  (Y x))
                             | _ -> circuit _ _ => constr:(fun x => beq_circuit (X x) (Y x))
                             end 

| fun x => pure_bset (@?X x) => constr:(fun x => fpure_bset (X x))

| fun x => exists (y:?T), @?B x y =>  let r := Refl (fun p => B (fst p) (snd p)) in
                       match T with
                       | bool => constr:(fun x => orb (r (x,true)) (r (x,false))) 
                       | {|§|} => constr:(fun x => orb (r (x,~0)) (orb (r (x,~1)) (r (x,~0))))
                       end

| fun x => @?P1 x /\ @?P2 x => let t1 := Refl P1 in
                               let t2 := Refl P2 in
                               constr:(fun x => andb (t1 x) (t2 x))

| fun x => @?P1 x \/ @?P2 x => let t1 := Refl P1 in
                               let t2 := Refl P2 in
                               constr:(fun x => orb (t1 x) (t2 x))

| fun x => not (@?P x) => let t := Refl P in
                      constr:(fun x => negb (t x))
end.

Ltac Reflect_step_g :=
match goal with
| [ |- ?P ?p1 ->( (step (?Ct ?p2) (?It ?p3) _ _) -> (?Q ?e))] 
     => let Pt := Refl P in
        let Qt := Refl Q in
        let X1 := fresh "X" in
        let X2 := fresh "X" in
        let X3 := fresh "X" in
        introv Prefl Hrefl;
        assert (X1: step_reflect_ptc Ct It Pt Qt = true) by (vm_compute; try easy);
        eapply step_reflect_ptc_safe
               with (Pp:=P) (Qp:=Q) (Pb:=Pt) (Qb:=Qt)
                    (C:=Ct) (I:=It) (p:=p1) (t:=snd(fst e)) (c:=snd e) in X1;
        [ cbn in X1; easy
        | introv X2; cbn in X2; PropimpBool X2
        | introv X3; cbn; cbv beta in X3; BoolimpProp X3 
        | easy
        | easy ] 
| [ |- ?P ?p1 ->( (stepg (?Ct ?p2) (?It ?p3) _ _) -> (?Q ?e))] 
     => let Pt := Refl P in
        let Qt := Refl Q in
        let X1 := fresh "X" in
        let X2 := fresh "X" in
        let X3 := fresh "X" in
        introv Prefl Hrefl;
        assert (X1: stepg_reflect_ptc Ct It Pt Qt = true) by (vm_compute; try easy);
        eapply stepg_reflect_ptc_safe 
               with (Pp:=P) (Qp:=Q) (Pb:=Pt) (Qb:=Qt)
                    (C:=Ct) (I:=It) (p:=p1) (t:=snd(fst e)) (c:=snd e) in X1;
        [ cbn in X1; easy
        | introv X2; cbn in X2; PropimpBool X2
        | introv X3; cbn; cbv beta in X3; BoolimpProp X3 
        | try (introv X2; Inverts X2); Checkpure
        | easy
        | easy ]
 end.

Ltac Reflo_step_g :=
match goal with
| [ |- ?P ?p1 ->( (step (?Ct ?p2) (?It ?p3) _ _) -> (?Q ?e))] 
     => let Pt := Refl P in
        let Qt := Refl Q in
        let X1 := fresh "X" in
        let X2 := fresh "X" in
        let X3 := fresh "X" in
        introv Prefl Hrefl;
        assert (X1: step_reflect_ptc Ct It Pt Qt = true) by (vm_compute; try easy);
        eapply step_reflect_ptc_safe 
               with (Pp:=P) (Qp:=Q) (Pb:=Pt) (Qb:=Qt)
                    (C:=Ct) (I:=It) (p:=p1) (t:=snd(fst e)) (c:=snd e) in X1;
        [ cbn in X1; easy
        | introv X2; cbn in X2; PropimpBool X2
        | introv X3; cbn; lazy beta in X3; BoolimpProp X3 
        | easy
        | easy ] 
| [ |- ?P ?p1 ->( (stepg (?Ct ?p2) (?It ?p3) _ _) -> (?Q ?e))] 
     => let Pt := Refl P in
        let Qt := Refl Q in
        let X1 := fresh "X" in
        let X2 := fresh "X" in
        let X3 := fresh "X" in
        introv Prefl Hrefl;
        assert (X1: stepg_reflo_ptc Ct It Pt Qt = true) by (vm_compute; try easy);
        eapply stepg_reflo_ptc_safe 
               with (Pp:=P) (Qp:=Q) (Pb:=Pt) (Qb:=Qt)
                    (C:=Ct) (I:=It) (p:=p1) (t:=snd(fst e)) (c:=snd e) in X1;
        [ cbn in X1; easy
        | introv X2; cbn in X2; PropimpBool X2
        | introv X3; cbn; lazy beta in X3; BoolimpProp X3 
        | try (introv X2; Inverts X2); Checkpure
        | easy
        | easy ]
 end.



(** For debugging purposes   

Definition Sel_not_Q A (Qb: A -> bool) (l:list A) : list A
           := filter (fun x => eqb (Qb x) false) l.

Definition where_false P S T (C:{|P|} -> circuit S T) (I:{|P|} -> {|S|})
                             (Pb : {|P|} -> bool) (Qb: Env_ptc P S T -> bool)
           := Sel_not_Q Qb (flat_map (fun p => let (t,lc) :=fsteps (C p) (I p) in
                                              List.map (fun c=>(p,t,c)) lc) (filterP Pb)).


Fixpoint fstepgst S T (c: circuit S T): {|S|} -> list ({|T|} * (circuit S T)):=
if is_wiring c then fun x => (redcomb c x, c)::nil else
match c with
| Cgate § § Not  => fun x => (redgate Not x, NOT)::nil 
| Cgate s t g   => fun x => List.map (fun x => (x, Cgate g)) (fintroglitch (redgate g x))
(*| Cgate s t p   => fun x => (redgate p x, Cgate p)::nil *)
| Cplug s t p   => fun x => (redplug p x, Cplug p)::nil
| Cseq s t u c1 c2   
  => fun x => let (t1,c1s) := fsteps c1 x in
              let  tc2s1   := List.map (fun c => (fst(snd c),(fst c) -o- (snd (snd c))))
                               (list_prod c1s (fstepgst c2 t1)) in
              let  tc1s    := fstepgst c1 x in
              let  tc2s2   := List.flat_map (fun x => let (t2s,c2s) := fsteps c2 (fst x) in
                                             List.map (fun c2' => (t2s,(snd x) -o- c2')) c2s) tc1s in
              tc2s1 ++ tc2s2
                               

| Cpar s t u v c1 c2 
  => fun x => let (t1,c1s) := fsteps c1 (fstS x)  in
              let (t2,c2s) := fsteps c2 (sndS x)  in
              let  tc1s    := fstepgst c1 (fstS x) in
              let  tc2s    := fstepgst c2 (sndS x) in
                  (List.map (fun c => ({t1,fst(snd c)},-|fst c,snd (snd c)|-)) (list_prod c1s tc2s))
               ++ (List.map (fun c => ({fst(fst c),t2},-|snd (fst c),snd c|-)) (list_prod tc1s c2s))


| Cloop s t b c      
  => fun x => let tcs1 := fstepgst c {x,bool2bset b} in
              let (t2,c2s) := fsteps c {x,~?} in
              List.flat_map (fun tc => match (sndS (fst tc)) with
                                       | ~0 => (fstS (fst tc),-{false}-(snd tc))::nil
                                       | ~1 => (fstS (fst tc),-{true}-(snd tc))::nil
                                       | ~? => (fstS (fst tc),-{false}-(snd tc))::
                                               (fstS (fst tc),-{true}-(snd tc))::nil
                                       | _  => nil
                                       end) (tcs1 ++ (List.map (fun c => (t2,c)) c2s))
end.



Definition my_reflect_ptc P S T (C:{|P|} -> circuit S T) (I:{|P|} -> {|S|})
                                   (Pb : {|P|} -> bool) 
                                   (Qb: Env_ptc P S T -> bool) 
           :=  flat_map (fun p => let ltc := fstepgst (C p) (I p) in
                                              List.map (fun tc => (p,fst tc,snd tc)) ltc)
                                    (filterP Pb).

Definition gen_all_cases P S T (C:{|P|} -> circuit S T) (I:{|P|} -> {|S|}) (Pb : {|P|} -> bool) 
           :=  flat_map (fun p => let ltc := fstepgst (C p) (I p) in
                                              List.map (fun tc => (p,fst tc,snd tc)) ltc)
                                    (filterP Pb).


Ltac Refli_step_g :=
match goal with
| [ |- ?P ?p1 ->( (stepg (?Ct ?p2) (?It ?p3) _ _) -> (?Q ?e))] 
     => let Pt := Refl P in
        let Qt := Refl Q in
        let X1 := fresh "X" in
        let X2 := fresh "X" in
        let X3 := fresh "X" in
        introv Prefl Hrefl;
        assert (X1: stepg_refli_ptc Ct It Pt Qt = true) by (vm_compute; try easy);
        eapply stepg_refli_ptc_safe 
               with (Pp:=P) (Qp:=Q) (Pb:=Pt) (Qb:=Qt)
                    (C:=Ct) (I:=It) (p:=p1) (t:=snd(fst e)) (c:=snd e) in X1;
        [ cbn in X1; easy
        | introv X2; cbn in X2; PropimpBool X2
        | introv X3; cbn; lazy beta in X3; BoolimpProp X3 
        | try (introv X2; Inverts X2); Checkpure
        | easy
        | easy ]
 end.


Ltac Reflect_debug :=
match goal with
| [ |- ?P ?p1 ->( (step (?Ct ?p2) (?It ?p3) _ _) -> (?Q ?e))] 
     => let Pt := Refl P in
        let Qt := Refl Q in
        let X1 := fresh "X" in
        let X2 := fresh "X" in
        let X3 := fresh "X" in
        introv Prefl Hrefl;
        assert (X1: step_reflect_ptc Ct It Pt Qt = true) 
 end.


Ltac ext1 :=
match goal with
| [ |- ?P ?p1 ->( (stepg (?Ct ?p2) (?It ?p3) _ _) -> (?Q ?e))] 
     => let Pt := Refl P in
        set (L:= filterP Pt)
 end.

Ltac ext2 :=
match goal with
| [ |- ?P ?p1 ->( (stepg (?Ct ?p2) (?It ?p3) _ _) -> (?Q ?e))] 
     => let Pt := Refl P in
        set (L:= flat_map (fun p => let ltc := fstepgs (Ct p) (It p) in
                                              List.map (fun tc => (p,fst tc,snd tc)) ltc)
                                    (filterP Pt))
 end.

Ltac ext3 :=
match goal with
| [ |- ?P ?p1 ->( (stepg (?Ct ?p2) (?It ?p3) _ _) -> (?Q ?e))] 
     => let Pt := Refl P in
        let Qt := Refl Q in
        assert (length (flat_map (fun p => let ltc := fstepgo (Ct p) (It p) in
                                              List.map (fun tc => (p,fst tc,snd tc)) ltc)
                                    (filterP Pt)) = 235)
 end.

Ltac ext4 :=
match goal with
| [ |- ?P ?p1 ->( (stepg (?Ct ?p2) (?It ?p3) _ _) -> (?Q ?e))] 
     => let Pt := Refl P in
        let Qt := Refl Q in
        assert (List.map Qt (flat_map (fun p => let ltc := fstepgs (Ct p) (It p) in
                                              List.map (fun tc => (p,fst tc,snd tc)) ltc)
                                    (filterP Pt)) = nil)
 end.

Ltac ext5 :=
match goal with
| [ |- ?P ?p1 ->( (stepg (?Ct ?p2) (?It ?p3) _ _) -> (?Q ?e))] 
     => let Pt := Refl P in
        let Qt := Refl Q in
        let X1 := fresh "X" in
        let X2 := fresh "X" in
        let X3 := fresh "X" in
        introv Prefl Hrefl;
        assert (X1: stepg_refli_ptc Ct It Pt Qt = true) by (vm_compute; try easy);
        eapply stepg_refli_ptc_safe 
               with (Pp:=P) (Qp:=Q) (Pb:=Pt) (Qb:=Qt)
                    (C:=Ct) (I:=It) (p:=p1) (t:=snd(fst e)) (c:=snd e) in X1
 end.


*)

