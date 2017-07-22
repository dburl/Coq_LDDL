
(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        Properties of the Semantic Relations (Functions)
#</h1>#    
#</center> <hr>#                                           *)
(*          Pascal Fradet - 2014_2015                      *)
(* ------------------------------------------------------- *)

Require Export Semantics.

Set Implicit Arguments.

(***********************************************************)
(** **       Properties of evaluation of basic gates       *)
(***********************************************************)
Lemma det_semgate : forall S T (g:gate S T) s t1 t2,
      semgate g s t1 -> semgate g s t2 -> t1 = t2.
Proof.
introv H1 H2. induction H1; Inverts H2; easy.
Qed.

Lemma redgate_pure : forall S T (g: gate S T) s t, 
                     pure_bset s -> redgate g s = t-> pure_bset t.
Proof.
introv P H. destruct g; Destruct_s s as s s'.
- destruct s; subst; easy.
- Destruct_s s as s. Destruct_s s' as s1. subst. Inverts P as P1 P2.
  destruct s; destruct s1; try  easy; Inverts P1; Inverts P2. 
- Destruct_s s as s. Destruct_s s' as s1. subst. Inverts P as P1 P2.
  destruct s; destruct s1; try  easy; Inverts P1; Inverts P2. 
Qed.

Lemma redplug_pure : forall S T (p: plug S T) s t, 
                     pure_bset s -> redplug p s = t -> pure_bset t.
Proof.
introv P H. destruct p; cbn in H.
- subst. easy.
- Inverts H. constructor; easy.
- Destruct_s s. Inverts H; Inverts P; try easy.
- Destruct_s s as s1 s3. Destruct_s s1 as s1 s2. Inverts H. cbn. 
  Inverts P as P1. Inverts P1. repeat constructor; easy.
- Destruct_s s as s1 s2. Destruct_s s2 as s2 s3. 
  Inverts H. Inverts P as P1 P2. Inverts P2. repeat constructor; easy.
Qed.

(***********************************************************)
(** ** Properties of one step (cycle) evaluation           *)
(***********************************************************)

Lemma step_pure : forall S T (c c': circuit S T) s t, 
                  pure_bset s -> step c s t c' -> pure_bset t.
Proof.
introv G H. induction H.
- eapply redgate_pure in H; easy.
- eapply redplug_pure in H; easy.
- easy.
- Inverts G. constructor; easy.
- assert (H1:pure_bset {s, bool2bset b}).
  + constructor; try easy. destruct b; easy.
  + apply IHstep in H1. Inverts H1. easy.
Qed.

(*the output signals and a circuit after a cycle both always exist*)
Lemma step_all_ex: forall S T (c:circuit S T) s,  
                   exists t, exists (c':circuit S T), step c s t c'.
Proof. 
introv. induction c.
- destruct g; eauto.
- destruct p; eauto.
- destruct IHc1 with s.
  destruct IHc2 with x. destruct H. destruct H0.
  exists x0 (x1 -o- x2). eauto.
- Destruct_s s. destruct IHc1 with x.
  destruct IHc2 with y. destruct H0. destruct H.
  exists {x0,x1} (-| x3, x2 |-). eauto. 
- destruct IHc with {s,bool2bset b}. destruct H. Destruct_s x.
  assert (exists b, bset2bool y b).
  + Destruct_s y. destruct x1.
    * exists false; easy.
    * exists true; easy.
    * exists true; easy.
  + destruct H0. eauto.
Qed. 

Lemma det_step_res : forall S T (c c1 c2:circuit S T) s t1 t2,
                     step c s t1 c1 -> step c s t2 c2 -> t1 = t2.
Proof.
introv H1 H2. induction H1; Inverts H2.
- easy.
- easy. 
- apply IHstep1 in H4; try easy. subst.
  apply IHstep2 in H9; easy.
- apply IHstep1 in H3; try easy.
  apply IHstep2 in H11; try easy. 
  subst. easy.
- apply IHstep in H10; try easy.
  Inverts H10. easy.
Qed.

Lemma det_step_cod : forall S T (c c1 c2:circuit S T) s t1 t2,
                     pure_bset s -> step c s t1 c1 -> step c s t2 c2 -> c1 = c2.
Proof.
introv I H1 H2. induction H1; Inverts H2.
- easy.
- easy.
- dupl H1_ H2. eapply det_step_res in H1_; try (exact H4). 
  apply IHstep1 in H4; try easy. subst.
  apply step_pure in H2; try easy.  
  apply IHstep2 in H9; try easy. subst. easy.
- Inverts I. apply IHstep1 in H3; try easy.
  apply IHstep2 in H11; try easy. 
  subst. easy.
- assert (X: pure_bset {s, bool2bset b}).
  + constructor. easy. destruct b; easy.
  + dupl H1 H2. eapply det_step_res in H1; try (exact H10).
    apply step_pure in H2; try easy.  
    apply IHstep in H10; try easy. Inverts H1. subst. 
    Inverts H2.
    Inverts H; Inverts H9; subst; try (easy || Inverts H6).
Qed.


Lemma det_step : forall S T (c c1 c2:circuit S T) s t1 t2,
      pure_bset s -> step c s t1 c1 -> step c s t2 c2 -> t1 = t2 /\ c1=c2.
Proof.
introv I H1 H2.
split.
- eapply det_step_res in H2. exact H2. exact H1.
- eapply det_step_cod in H2. exact H2. exact I. exact H1.
Qed.


Lemma redgate_imp_redgateB : forall S T (g:gate S T) s t a b,
                             pure_bset s -> bset2bsig s a -> bset2bsig t b 
                          -> redgate g s = t -> redgateB g a = b.
Proof.
introv H B1 B2 P. destruct g.
- Destruct_b a. destruct x; Inverts P; Inverts H; Inverts B1; Inverts B2; try easy.
- Destruct_s s as x y. Destruct_s x as x. Destruct_s y as y.
  destruct x; destruct y; Inverts H; Inverts B1; 
  Inverts B2; Inverts H2; Inverts H7; Inverts H5; Inverts H; Inverts H3; try Inverts H5; easy. 
- Destruct_s s as x y. Destruct_s x as x. Destruct_s y as y.
  destruct x; destruct y; Inverts P; Inverts H; Inverts B1; 
  Inverts B2; Inverts H4; Inverts H6; Inverts H8; Inverts H3; try easy.
Qed.

Lemma redplug_imp_redplugB : forall S T (p:plug S T) s t a b,
                             pure_bset s -> bset2bsig s a -> bset2bsig t b 
                          -> redplug p s = t -> redplugB p a = b.
Proof.
introv H B1 B2 P. destruct p; cbn in *.
- subst. eapply det_bset2bsig in B2; try exact H; try exact B1. easy.
- Inverts P. Inverts B2.  
  eapply det_bset2bsig in H4; try exact H; try exact B1.
  eapply det_bset2bsig in H7; try exact H; try exact B1. 
  subst. subst. easy.
- Inverts P. Inverts B1. Inverts B2. Inverts H.
  eapply det_bset2bsig in H4; try easy; try (exact H6). subst.
  eapply det_bset2bsig in H9; try easy; try (exact H5). subst.
  easy.
- Inverts H. Inverts P. Inverts H3. 
  Inverts B1. Inverts H3. 
  Inverts B2. Inverts H12. cbn. 
  eapply det_bset2bsig in H3; try easy; try (exact H7). subst.
  eapply det_bset2bsig in H8; try easy; try (exact H11). subst.
  eapply det_bset2bsig in H9; try easy; try (exact H14). subst.
  easy.
- Inverts H. Inverts P. Inverts H4. 
  Inverts B1. Inverts H9. 
  Inverts B2. Inverts H8. cbn. 
  eapply det_bset2bsig in H4; try easy; try (exact H9). subst.
  eapply det_bset2bsig in H12; try easy; try (exact H11). subst.
  eapply det_bset2bsig in H7; try easy; try (exact H14). subst.
  easy.
Qed.


(* this lemma should not be needed but I do not know how to name results of fstepB *)
 
Lemma fstepB_react : forall S T (c:circuit S T) a, exists c' b, fstepB c a = (b,c').
Proof.
introv.
exists (snd (fstepB c a)). exists (fst (fstepB c a)). 
destruct (fstepB c a). easy.
Qed.


Lemma step_imp_fstepB : forall S T (c c':circuit S T) s t a b,
                       pure_bset s -> step c s t c' 
                    -> bset2bsig s a -> bset2bsig t b 
                    -> fstepB c a = (b,c').
Proof.
introv P H B1 B2.
induction c.
- Inverts H. cbn.
  apply injective_projections; cbn; try easy.
  eapply redgate_imp_redgateB in B2; try exact B2; try exact B1; easy.
- Inverts H. cbn.
  apply injective_projections; cbn; try easy.
  eapply redplug_imp_redplugB in B2; try exact B2; try exact B1; easy.
- Inverts H.
  dupl H4 H5. apply step_pure in H5; try easy.
  set (H1:= ex_bsig t0). destruct H1 as [b0 H1].
  eapply IHc1 in H4; try (exact B1); try (exact H1); try easy.
  eapply IHc2 in H9; try (exact B2); try (exact H1); try easy.
  cbn. rewrite H4. rewrite H9. easy.
- Inverts H. Inverts P. Inverts B1. Inverts B2.
  eapply IHc1 in H3; try (exact H4); try (exact H6); try easy.
  eapply IHc2 in H10; try (exact H8); try (exact H11); try easy.
  cbn. rewrite H3. rewrite H10. easy. 
- Inverts H. 
  assert (H1: pure_bset {s, bool2bset b0}). 
     constructor. easy. apply b2t_is_pure.
  assert (H2: bset2bsig {s, bool2bset b0} [a,^b0]).
     constructor; destruct b0; easy.
  assert (H3: bset2bsig {t, a0} [b,^b']).
     constructor. easy. Inverts H7; easy.
  eapply IHc in H8; try (exact H1); try (exact H2); try (exact H3). 
  cbn. unfold bool2bsig. rewrite H8. easy.
Qed.

Lemma redgateB_imp_redgate : forall S T (g:gate S T) b,
                             redgate g (bsig2bset b) =  bsig2bset (redgateB g b).
Proof.
introv. destruct g.
- Destruct_b b as b.  
  destruct b; constructor.
- Destruct_b b as x y. Destruct_b x as x. Destruct_b y as y.
  destruct x; destruct y; subst; constructor.
- Destruct_b b as x y. Destruct_b x as x. Destruct_b y as y.
  destruct x; destruct y; subst; constructor. 
Qed.

Lemma redplugB_imp_redplug : forall S T (p:plug S T) b,
                             redplug p (bsig2bset b) =  bsig2bset (redplugB p b).
Proof.
introv. destruct p.
- easy. 
- easy. 
- Destruct_b b. easy. 
- Destruct_b b as x y. Destruct_b x. easy. 
- Destruct_b b as x y. Destruct_b y. easy.
Qed.


Lemma fstepB_imp_step : forall S T (c c':circuit S T) a b,
                        fstepB c a = (b,c') -> step c (bsig2bset a) (bsig2bset b) c'.
Proof.
introv H. induction c.
- Inverts H. rewrite <- redgateB_imp_redgate. easy.
- Inverts H. rewrite <- redplugB_imp_redplug. easy.
- set (H1:=fstepB_react c1 a). destruct H1 as [c'1 [a' H1]].
  set (H2:=fstepB_react c2 a'). destruct H2 as [c'2 [b' H2]].
  Inverts H. rewrite H1 in H3. rewrite H2 in H3. Inverts H3.
  apply IHc1 in H1. apply IHc2 in H2.
  econstructor. exact H1. exact H2.
- Destruct_b a as a1 a2. 
  set (H1:=fstepB_react c1 a1). destruct H1 as [c'1 [b1 H1]].
  set (H2:=fstepB_react c2 a2). destruct H2 as [c'2 [b2 H2]].
  Inverts H. rewrite H1 in H3. rewrite H2 in H3. Inverts H3.
  apply IHc1 in H1. apply IHc2 in H2.
  easy. 
- set (H1:=fstepB_react c [a,bool2bsig b0]). destruct H1 as [c'1 [b1 H1]].
  Inverts H. rewrite H1 in H2. Inverts H2.
  apply IHc in H1. Destruct_b b1 as b1 b2. cbn. 
  apply Sloop with (a:=bsig2bset b2).
  + Destruct_b b2 as b.
    destruct b; easy. 
  + cbn in H1. destruct b0; easy. 
Qed.

Corollary fstepB_imp_step' : forall S T (c :circuit S T) b,
                             step c (bsig2bset b) (bsig2bset (fst (fstepB c b))) (snd (fstepB c b)).
Proof.
introv.
set (H:=fstepB_react c b). destruct H as [c' [b' H]].
rewrite H. cbn. apply fstepB_imp_step. easy.
Qed.

(***********************************************************)
(** **  Relations between the different notion of steps    *)
(***********************************************************)

Lemma step_imp_stepg : forall S T (c c': circuit S T) s t, 
                        step c s t c' -> stepg c s t c'.
Proof. introv H. induction H; econstructor; try easy.
- subst. easy.
- exact IHstep1.
- easy.
- exact H.
- easy.
Qed.

Lemma stepg_imp_stepglitch : forall S T (c c': circuit S T) s t, 
                             stepg c s t c' -> stepglitch c s t c'.
Proof. introv H. apply Safterlg. easy. Qed.


(***********************************************************)
(** **  Properties of reduction of combinatorial circuits  *)
(***********************************************************)

Lemma step_comb_cir : forall S T (c c': circuit S T) s t, 
                     combinatorial c -> step c s t c' -> c=c' .
Proof.
introv C H. induction H.
- easy.
- easy.
- Inverts C. apply IHstep1 in H5. apply IHstep2 in H7. subst. easy.
- Inverts C. apply IHstep1 in H4. apply IHstep2 in H8. subst. easy.
- Inverts C.
Qed.

Lemma step_notcomb : forall S T (c c': circuit S T) s t, 
                     ~combinatorial c -> step c s t c' -> ~combinatorial c' .
Proof.
introv C H. induction H; intro C1.
- easy.
- easy.
- destruct (dec_comb c1) as [H1|H1]; destruct (dec_comb c2) as [H2|H2]; apply C.
  + constructor; easy.
  + apply IHstep2 in H2. Inverts C1. false. 
  + apply IHstep1 in H1. Inverts C1. false. 
  + apply IHstep2 in H2. Inverts C1. false. 
- destruct (dec_comb c1) as [H1|H1]; destruct (dec_comb c2) as [H2|H2]; apply C.
  + constructor; easy.
  + apply IHstep2 in H2. Inverts C1. false. 
  + apply IHstep1 in H1. Inverts C1. false. 
  + apply IHstep2 in H2. Inverts C1. false. 
- Inverts C1.
Qed.

Lemma stepg_comb_cir : forall S T (c c': circuit S T) s t, 
                       combinatorial c -> stepg c s t c' -> c=c' .
Proof.
introv C H. induction H; try easy; Inverts C.
- apply IHstepg in H5. 
  apply step_comb_cir in H0; try easy. subst. easy.
- apply IHstepg in H7. 
  apply step_comb_cir in H; try easy. subst. easy.
- apply IHstepg in H4. 
  apply step_comb_cir in H0; try easy. subst. easy.
- apply IHstepg in H8. 
  apply step_comb_cir in H; try easy. subst. easy.
Qed.

Lemma stepglitch_comb_cir : forall S T (c c': circuit S T) s t, 
                            combinatorial c -> stepglitch c s t c' -> c=c' .
Proof.
introv C H. Inverts H.
- apply step_comb_cir in H7; easy.
- apply stepg_comb_cir in H6; easy.
Qed.


Lemma redgate_equiv_semgate : forall S T (g: gate S T) s t, 
                              redgate g s = t <-> semgate g s t.
Proof.
split; introv H.
- destruct g; cbn in H; subst; constructor.
- destruct g; Inverts H; easy.
Qed.

Lemma redplug_equiv_semplug : forall S T (p: plug S T) s t, 
                              redplug p s = t <-> semplug p s t.
Proof.
split; introv H.
- destruct p; cbn in H; subst; try constructor. 
  + Destruct_s s. constructor.
  + Destruct_s s as s1 s2. Destruct_s s1. constructor.
  + Destruct_s s as s1 s2. Destruct_s s2. constructor. 
- destruct p; Inverts H; easy.
Qed.

Lemma sem_red_gate : forall S T (g: gate S T) s, semgate g s (redgate g s).
Proof. intros. destruct g; constructor. Qed.

Lemma sem_red_plug : forall S T (p: plug S T) s, semplug p s (redplug p s).
Proof.
intros. destruct p; cbn; try constructor.
- Destruct_s s. constructor. 
- Destruct_s s as s1 s2. Destruct_s s1. constructor.
- Destruct_s s as s1 s2. Destruct_s s2. constructor.
Qed.

Lemma comb_imp_redef : forall S T (c: circuit S T) s, combinatorial c -> exists t, redcomb c s = t.
Proof.
introv H. induction  H.
- destruct g. 
  + exists (negS s). easy.
  + exists (andS s). easy.
  + exists (orS s). easy.
- destruct p.
  + exists s. easy.
  + exists {s,s}. easy.
  + exists {sndS s,fstS s}. easy.
  + exists {fstS (fstS s), {sndS (fstS s),sndS s}}. easy.
  + exists {{fstS s, fstS (sndS s)},sndS (sndS s)}. easy.
- destruct (IHcombinatorial1 s) as [t1 R1].
  destruct (IHcombinatorial2 t1) as [t ?].
  exists t. cbn. rewrite R1. easy.
- destruct (IHcombinatorial1 (fstS s)) as [t1 R1].
  destruct (IHcombinatorial2 (sndS s)) as [t2 R2].
  exists {t1,t2}. cbn. rewrite R1. rewrite R2. easy.
Qed.

Lemma redcomb_imp_step : forall S T (c: circuit S T) s t, 
                         combinatorial c -> redcomb c s = t -> step c s t c.
Proof.
introv C H. induction c; Inverts C.
- subst. easy. 
- subst. easy. 
- dupl H4 H1. dupl H6 H7.
  apply comb_imp_redef with (s:=s) in H4. destruct H4 as [t1 H4].
  apply comb_imp_redef with (s:=t1) in H6. destruct H6 as [t2 H6].
  cbn in H. dupl H4 H2. 
  apply IHc1 in H4; try easy. eapply Sseq. exact H4.
  apply IHc2; try easy. congruence.
- Destruct_s s as s1 s2. cbn in H.
  dupl H3 C1. apply comb_imp_redef with (s:=s1) in H3. 
  destruct H3 as [t1 H3]. rewrite H3 in H.
  dupl H7 C2. apply comb_imp_redef with (s:=s2) in H7. destruct H7 as [t2 H7].
  rewrite H7 in H. Inverts H.
  constructor; easy.
Qed.

Lemma step_imp_redcomb : forall S T (c c': circuit S T) s t, 
                         combinatorial c -> step c s t c' -> redcomb c s = t.
Proof.
introv C H. dependent induction H; Inverts C.
- easy.
- easy.
- apply IHstep1 in H5.
  cbn. rewrite H5. easy.
- apply IHstep1 in H4. apply IHstep2 in H8.
  cbn. rewrite H4; rewrite H8. easy.
Qed.

Lemma redcomb_equiv_step : forall S T (c: circuit S T) s t, 
                           combinatorial c -> (redcomb c s = t <-> step c s t c).
Proof.
introv C. split. 
- apply redcomb_imp_step. easy. 
- apply step_imp_redcomb. easy. 
Qed. 

Lemma stepredcomb :  forall S T (c: circuit S T) s, combinatorial c -> step c s (redcomb c s) c.
Proof. introv C. apply redcomb_imp_step; easy. Qed.


Lemma wiring_equ_step_g : forall S T (c c': circuit S T) s t, 
                          wiring c -> (step c s t c' <-> stepg c s t c').
Proof.
introv I. split.
- induction 1; try Inverts I. 
  + constructor. easy. 
  + econstructor. apply IHstep1; easy. easy.
  + econstructor. apply IHstep1. easy. easy.
- induction 1; try Inverts I.
  + constructor. easy.
  + econstructor.
    apply IHstepg. easy. easy.
  + econstructor.
    exact H. apply IHstepg. easy.
  + econstructor.
    apply IHstepg. easy. easy.
  + econstructor.
    exact H. apply IHstepg. easy.
Qed.


 
(** About functional evaluation of any circuits (with an option type)  *)

Lemma fstep_imp_step : forall S T (c c':circuit S T) s t, fstep c s = Some (t,c') -> step c s t c'.
Proof.
induction c; introv H.
- Inverts H. easy.
- Inverts H. easy.
- Inverts H.
  assert (F1:(exists (t1: {|T|}), exists (c1' : circuit S T), fstep c1 s = Some (t1,c1'))).
  destruct (fstep c1 s). destruct p. exists b c. easy. Inverts H1.
  destruct F1 as [t1 [c1' F1]]. rewrite F1 in H1.  apply IHc1 in F1. 
  assert (F2:(exists (t2: {|U|}), exists (c2' : circuit T U), fstep c2 t1 = Some (t2,c2'))).
  destruct (fstep c2 t1). destruct p. exists b c. easy. Inverts H1.
  destruct F2 as [t2 [c2' F2]]. rewrite F2 in H1. apply IHc2 in F2.
  Inverts H1. econstructor. exact F1. easy.
- Inverts H.
  assert (F1:(exists (t1: {|T|}), exists (c1' : circuit S T), fstep c1 (fstS s) = Some (t1,c1'))).
  destruct (fstep c1 (fstS s)). destruct p. exists b c. easy. Inverts H1.
  destruct F1 as [t1 [c1' F1]]. rewrite F1 in H1.  apply IHc1 in F1. 
  assert (F2:(exists (t2: {|V|}), exists (c2' : circuit U V), fstep c2 (sndS s) = Some (t2,c2'))).
  destruct (fstep c2 (sndS s)). destruct p. exists b c. easy. Inverts H1.
  destruct F2 as [t2 [c2' F2]]. rewrite F2 in H1. apply IHc2 in F2.
  Inverts H1. Destruct_s s. econstructor. exact F1. easy.
- Inverts H.
  assert (F1:(exists (t: {|T # §|}), exists (c':circuit (S # §) (T # §)), fstep c {s, bool2bset b} = Some (t,c'))).
  destruct (fstep c {s, bool2bset b}). destruct p. exists b0 c0. easy. Inverts H1.
  destruct F1 as [t1 [c1' F1]]. rewrite F1 in H1.  apply IHc in F1.
  Destruct_s t1 as t1 t2. cbn in H1. Destruct_s t2 as x.
  destruct x; Inverts H1.
  + econstructor; try exact F1; easy.
  + econstructor; try exact F1; easy.
Qed.

Lemma fstep_imp_detstep : forall S T (c c1 c2:circuit S T) s t1 t2,
                          fstep c s = Some (t1,c1) -> step c s t2 c2 -> t1=t2 /\ c1=c2.
Proof.
introv G H. induction H; Inverts G.
- easy.
- easy. 
- assert (F1:(exists (x1: {|T|}), exists (y1 : circuit S T), fstep c0 s = Some (x1,y1))).
  destruct (fstep c0 s). destruct p. exists b c. easy. Inverts H2.
  destruct F1 as [t11 [c11 F1]]. rewrite F1 in H2.
  assert (F2:(exists (x2: {|U|}), exists (y2 : circuit T U), fstep c2 t11 = Some (x2,y2))).
  destruct (fstep c2 t11). destruct p. exists b c. easy. Inverts H2.
  destruct F2 as [t22 [c22 F2]]. rewrite F2 in H2. Inverts H2.
  apply IHstep1 in F1. destruct F1 as [? F1]; subst.
  apply IHstep2 in F2. destruct F2 as [? F2]; subst. easy.
- assert (F1:(exists (x1: {|T|}), exists (y1 : circuit S T), fstep c0 s = Some (x1,y1))).
  destruct (fstep c0 s). destruct p. exists b c. easy. Inverts H2.
  destruct F1 as [t11 [c11 F1]]. rewrite F1 in H2.
  assert (F2:(exists (x2: {|V|}), exists (y2 : circuit U V), fstep c2 u = Some (x2,y2))).
  destruct (fstep c2 u). destruct p. exists b c. easy. Inverts H2.
  destruct F2 as [t22 [c22 F2]]. rewrite F2 in H2. Inverts H2.
  apply IHstep1 in F1. destruct F1 as [? F1]; subst.
  apply IHstep2 in F2. destruct F2 as [? F2]; subst. easy.
- assert (F1:(exists (t: {|T # §|}), exists (c':circuit (S # §) (T # §)), fstep c {s, bool2bset b} = Some (t,c'))).
  destruct (fstep c {s, bool2bset b}). destruct p. exists b0 c0. easy. Inverts H2.
  destruct F1 as [t11 [c11 F1]]. rewrite F1 in H2.  apply IHstep in F1.
  destruct F1 as [F1 ?]. subst. cbn in H2. 
  Destruct_s a as a. destruct a; Inverts H2; Inverts H; easy.
Qed.

(** * General properties about corruption  *)

Lemma step_onefault : forall S T (c c':circuit S T) s t,
                       atmost1glitch s
                    -> nofork_circuit c
                    -> step c s t c'
                    -> atmost1glitch t.
Proof.
introv I J H. induction H.
- destruct g; constructor.
- destruct p.
  + cbn in H. subst. easy.
  + Inverts J.
  + Inverts H. Inverts I; easy. 
  + Inverts H. Inverts I; Inverts H3; easy.
  + Inverts H. Inverts I; Inverts H4; easy.
- Inverts J. easy. 
- Inverts I; Inverts J. 
  + constructor. apply IHstep1 in H4; try easy. 
    eapply step_pure. exact H6. exact H0.
  + apply step_pure with (c:=c1) (c':=c1') (t:=t) in H4; easy.
- assert (X:atmost1glitch {s, bool2bset b}). 
  constructor. easy. destruct b; easy. 
  apply IHstep in X. Inverts X. easy.
  apply pure_imp_atmost1. easy. Inverts J. easy.
Qed.

Lemma stepg_am1fault : forall S T (c c':circuit S T) s t,
                       pure_bset s
                    -> nofork_circuit c
                    -> stepg c s t c'
                    -> atmost1glitch t.
Proof.
introv I J H. induction H.
- assert (X: redgate g s = redgate g s) by easy.
  eapply redgate_pure with (g:=g) in I; try exact X. 
  eapply intro_imp_atmost1 in H; try easy.
- eapply redplug_pure with (p:=p) in H; try easy. 
  apply pure_imp_atmost1. easy.
- Inverts J. apply IHstepg in I; try easy.
  eapply step_onefault in I. exact I. exact H7. exact H0.
- eapply step_pure in I.
  eapply IHstepg in I. easy. Inverts J. easy. exact H. 
- Inverts I; Inverts J.
  apply IHstepg in H4. 
  apply step_pure with (c:=c2) (c':=c2') (t:=v) in H6; easy.
  easy.
- Inverts I; Inverts J.
  apply IHstepg in H6. 
  apply step_pure with (c:=c1) (c':=c1') (t:=t) in H4; easy.
  easy.
- assert (X:pure_bset {s, bool2bset b}). 
  constructor. easy. destruct b; easy. 
  apply IHstepg in X. Inverts X. easy.
  apply pure_imp_atmost1. easy. Inverts J. easy.
- eapply step_onefault in H1.
  + Inverts H1; try easy. apply pure_imp_atmost1. easy.
  + apply Am1g_3. easy. eapply intro_imp_atmost1 in H; try easy.
    apply b2t_is_pure.
  + Inverts J. easy.    
Qed.

Lemma ig_imp_emG : forall S s1 s2, @introglitch S s1 s2 -> eq_mod_G s1 s2.
Proof. introv I. induction I; try easy.
- constructor; try easy. apply eq_mod_G_refl.
- constructor; try easy. apply eq_mod_G_refl.
- apply eq_mod_G_refl. 
Qed. 

Lemma emG_ig : forall S s t u, @eq_mod_G S s t -> introglitch t u -> eq_mod_G s u.
Proof.
introv E I. induction E.
- apply ig_imp_emG. easy.
- easy.
- Inverts I. easy.
- Inverts I. 
  + apply IHE1 in H0. easy.
  + apply IHE2 in H0. easy.
  + easy.
Qed.


Lemma redgate_eqmodG : forall S T (g: gate S T) s s',
                        eq_mod_G s s'
                     -> eq_mod_G (redgate g s) (redgate g s').
Proof.
introv H. destruct g.
- Destruct_s s as s. Destruct_s s' as s'.
  destruct s; destruct s'; try easy; Inverts H; Inverts H0.
- Destruct_s s as s1 s2. Destruct_s s' as s'1 s'2.
  Destruct_s s1 as s1. Destruct_s s2 as s2.
  Destruct_s s'1 as s'1. Destruct_s s'2 as s'2.
  destruct s1; destruct s2; destruct s'1; destruct s'2; 
  try easy; Inverts H; easy.
- Destruct_s s as s1 s2. Destruct_s s' as s'1 s'2.
  Destruct_s s1 as s1. Destruct_s s2 as s2.
  Destruct_s s'1 as s'1. Destruct_s s'2 as s'2.
  destruct s1; destruct s2; destruct s'1; destruct s'2; 
  try easy; Inverts H; easy.
Qed.

Lemma semgate_eqmodG : forall S T (g: gate S T) s s' t t',
                        eq_mod_G s s'
                     -> semgate g s t
                     -> semgate g s' t'
                     -> eq_mod_G t t'.
Proof.
introv E H1 H2. induction H1; Inverts H2; try easy.
- Inverts E; easy.
- Inverts E. 
  Destruct_s s1 as s1. Destruct_s s2 as s2.
  Destruct_s t1 as t1. Destruct_s t2 as t2.
  destruct s1; destruct s2; destruct t1; destruct t2; easy.
- Inverts E. 
  Destruct_s s1 as s1. Destruct_s s2 as s2.
  Destruct_s t1 as t1. Destruct_s t2 as t2.
  destruct s1; destruct s2; destruct t1; destruct t2; easy.
Qed.


Lemma redplug_eqmodG : forall S T (p: plug S T) s s',
                        eq_mod_G s s'
                     -> eq_mod_G (redplug p s) (redplug p s').
Proof.
introv H. destruct p.
- easy.
- easy.
- Inverts H. easy.
- Inverts H. Inverts H4. easy.
- Inverts H. Inverts H5. easy.
Qed.

Lemma semplug_eqmodG : forall S T (p: plug S T) s s' t t',
                        eq_mod_G s s'
                     -> semplug p s t
                     -> semplug p s' t'
                     -> eq_mod_G t t'.
Proof.
introv E H1 H2. induction H1; Inverts H2; try easy.
- Inverts E; easy.
- Inverts E. Inverts H2. easy.
- Inverts E. Inverts H6. easy.
Qed.

Lemma step_eqmodG : forall S T (c c' c'':circuit S T) s s' t t',
                        eq_mod_G s s'
                     -> step c s t c'
                     -> step c s' t' c''
                     -> eq_mod_G t t'.
Proof.
introv E H1 H2. induction H1; Inverts H2.
- rewrite <- H. eapply semgate_eqmodG with (g:=g); try exact E; apply sem_red_gate.
- rewrite <- H. eapply semplug_eqmodG with (p:=p); try exact E; try apply sem_red_plug.
- apply IHstep1 in H4; try easy.
  eapply IHstep2. exact H4. exact H9.
- Inverts E.
  apply IHstep1 in H3; try easy.
  apply IHstep2 in H10; try easy.
- assert (X:eq_mod_G {s, bool2bset b} {s', bool2bset b}) by easy.
  eapply IHstep in X; try (exact H10). Inverts X. easy.
Qed.

Lemma step_g_eqmodG : forall S T (c c' c'':circuit S T) s s' t t',
                        eq_mod_G s s'
                     -> step c s t c'
                     -> stepg c s' t' c''
                     -> eq_mod_G t t'.
Proof.
introv E H1 H2. induction H1.
- rewrite <- H. Inverts H2. apply redgate_eqmodG with (g:=g) in E. 
  eapply emG_ig. exact E. easy. 
- rewrite <- H. Inverts H2. apply redplug_eqmodG. easy.
- Inverts H2.
  + apply IHstep1 in H4; try easy.
    eapply step_eqmodG in H9; try (exact H1_0); try (exact H4).
    easy.
  + eapply step_eqmodG in H4; try (exact H1_); try (exact E).
    eapply IHstep2. exact H4. exact H9.
- Inverts H2; Inverts E.
  + apply IHstep1 in H3; try easy.
    eapply step_eqmodG in H10; try (exact H7); try (exact H1_0). 
    easy.
  + apply IHstep2 in H10; try easy.
    eapply step_eqmodG in H3; try (exact H12); try (exact H1_); easy. 
- Inverts H2.
  + assert (X:eq_mod_G {s, bool2bset b} {s', bool2bset b}) by easy.
    eapply IHstep in X; try (exact H10). Inverts X. easy.
  + eapply step_eqmodG in H11; try exact H1.
    Inverts H11. easy.
    constructor. easy.
    apply emG_ig with (t:= bool2bset b); easy.
Qed.


(***********************************************************)
(** **  Properties on circuit evaluation (Stream -> Stream)*)
(***********************************************************)

Lemma set1K_n_imp_set1K_0  : forall S T (c:circuit S T) K n Pis Pos, 
                             set1K_eval K c n Pis Pos 
                          -> set1K_eval K c 0 Pis Pos.
Proof.
cofix CIH.
introv H.
destruct Pis. inverts H.
- eapply set1K_eval1. exact H7. apply CIH with (n:=pred n). easy.
- eapply set1K_eval2. exact H7. 
  exact H8. 
Qed.

