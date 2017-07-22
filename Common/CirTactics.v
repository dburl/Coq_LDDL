
(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        Some tactics to reduce, simplify circuits
#</h1>#
#</center> <hr>#                                           *)
(*          Pascal Fradet - 2014_2015                      *)
(* ------------------------------------------------------- *)

Require Export PropSem.

Set Implicit Arguments.

(* ####################################################### *)
(** *           Some lemmas used in tactics                *)
(* ####################################################### *)

(** **      Inversion theorems for step and stepg          *)

Lemma inv_stepS : forall S T U (c1:circuit S T) (c2:circuit T U) s u c',
                  step (c1 -o- c2) s u c'
               -> exists c1', exists c2', exists t,
                  step c1 s t c1' /\ step c2 t u c2' /\ c'=c1'-o-c2'.
Proof. introv G. Inverts G. exists c1' c2' t. easy. Qed.

Lemma inv_stepP : forall S T U V (c1:circuit S T) (c2:circuit U V) su tv c',
                  step (-|c1,c2|-) su tv c'
               -> exists c1', exists c2', exists t, exists v,
                  step c1 (fstS su) t c1' /\ step c2 (sndS su) v c2'
               /\ fstS tv = t /\ sndS tv = v /\ c'=-|c1',c2'|-.
Proof. introv H. Inverts H. exists c1' c2' t v. easy. Qed.

Lemma inv_stepL : forall S T (c:circuit (S# §) (T#§)) b s t c1,
                  step (-{b}-c) s t c1
               -> exists c', exists a, exists b',
                  step c {s,bool2bset b} {t,a} c'
               /\ bset2bool a b' /\ c1=-{b'}-c'.
Proof. introv H. Inverts H. exists c' a b'. easy. Qed.


Lemma inv_stepId : forall S (s t:{|S|}) c,
                   step (ID) s t c -> t=s /\ c=ID.
Proof. introv H. Inverts H. easy. Qed.

Lemma inv_stepFo : forall S (s:{|S|}) t c,
                   step (FORK) s t c -> fstS t=s /\ sndS t = s /\ c=FORK.
Proof. introv H. Inverts H. easy. Qed.

Lemma inv_stepSw : forall S T (s:{|S#T|}) t c,
                   step (SWAP) s t c -> fstS t= sndS s /\ sndS t = fstS s /\ c=SWAP.
Proof. introv H. Inverts H. easy. Qed.

Lemma inv_stepLs : forall S T U (s:{|S#T#U|}) t c,
                   step (LSH) s t c -> fstS t=fstS (fstS s) /\ fstS (sndS t) = sndS (fstS s)
                                    /\ sndS (sndS t) = sndS s /\ c=LSH.
Proof. introv H. Inverts H. easy. Qed.

Lemma inv_stepRs : forall S T U (s:{|S#(T#U)|}) t c,
                   step (RSH) s t c -> fstS (fstS t)=fstS s /\ sndS (fstS t)=fstS (sndS s)
                                    /\ sndS t=sndS (sndS s) /\ c=RSH.
Proof. introv H. Inverts H. easy. Qed.



Lemma inv_stepgS : forall S T U (c1:circuit S T) (c2:circuit T U) s u c',
                   stepg (c1 -o- c2) s u c'
                -> (exists c1', exists c2', exists t,
                    stepg c1 s t c1' /\ step c2 t u c2' /\ c'=c1'-o-c2')
                \/ (exists c1', exists c2', exists t,
                    step c1 s t c1' /\ stepg c2 t u c2' /\ c'=c1'-o-c2').
Proof.
introv H. Inverts H.
- left. exists c1' c2' t. easy.
- right. exists c1' c2' t. easy.
Qed.


Lemma inv_stepgS1 : forall S T U (c1:circuit S T) (c2:circuit T U) s u c',
                    wiring c1 -> stepg (c1 -o- c2) s u c'
                ->  exists c1', exists c2', exists t,
                    step c1 s t c1' /\ stepg c2 t u c2' /\ c'=c1'-o-c2'.
Proof.
introv W H. Inverts H.
- apply wiring_equ_step_g in H4; try easy.
  exists c1' c2' t.
  apply step_imp_stepg in H9.
  easy.
- exists c1' c2' t.
  easy.
Qed.

Lemma inv_stepgS2 : forall S T U (c1:circuit S T) (c2:circuit T U) s u c',
                    wiring c2 -> stepg (c1 -o- c2) s u c'
                ->  exists c1', exists c2', exists t,
                    stepg c1 s t c1' /\ step c2 t u c2' /\ c'=c1'-o-c2'.
Proof.
introv W H. Inverts H.
- exists c1' c2' t.
  easy.
- apply wiring_equ_step_g in H9; try easy.
  exists c1' c2' t.
  apply step_imp_stepg in H4.
  easy.
Qed.


Lemma inv_stepgP : forall S T U V (c1:circuit S T) (c2:circuit U V) su tv c',
                   stepg (-|c1,c2|-) su tv c'
                -> (exists c1', exists c2', exists t, exists v,
                    stepg c1 (fstS su) t c1' /\ step c2 (sndS su) v c2'
                    /\ fstS tv = t /\ sndS tv = v /\ c'=-|c1',c2'|-)
                \/ (exists c1', exists c2', exists t, exists v,
                    step c1 (fstS su) t c1' /\ stepg c2 (sndS su) v c2'
                    /\ fstS tv = t /\ sndS tv = v /\ c'=-|c1',c2'|-).
Proof.
introv H. Inverts H.
- left. exists c1' c2' t v. easy.
- right. exists c1' c2' t v. easy.
Qed.

Lemma inv_stepgP1 : forall S T U V (c1:circuit S T) (c2:circuit U V) su tv c',
                   wiring c1 -> stepg (-|c1,c2|-) su tv c'
                -> (exists c1', exists c2', exists t, exists v,
                    step c1 (fstS su) t c1' /\ stepg c2 (sndS su) v c2'
                    /\ fstS tv = t /\ sndS tv = v /\ c'=-|c1',c2'|-).
Proof.
introv W H. Inverts H.
- apply wiring_equ_step_g in H3; try easy.
  exists c1' c2' t v.
  apply step_imp_stepg in H10.
  easy.
- exists c1' c2' t v. easy.
Qed.

Lemma inv_stepgP2 : forall S T U V (c1:circuit S T) (c2:circuit U V) su tv c',
                   wiring c2 -> stepg (-|c1,c2|-) su tv c'
                -> (exists c1', exists c2', exists t, exists v,
                    stepg c1 (fstS su) t c1' /\ step c2 (sndS su) v c2'
                    /\ fstS tv = t /\ sndS tv = v /\ c'=-|c1',c2'|-).
Proof.
introv W H. Inverts H.
- exists c1' c2' t v. easy.
- apply wiring_equ_step_g in H10; try easy.
  exists c1' c2' t v.
  apply step_imp_stepg in H3.
  easy.
Qed.

Lemma inv_stepgL : forall S T (c:circuit (S# §) (T#§)) b s t c1,
                   stepg (-{b}-c) s t c1
                ->  (exists c', exists a, exists b',
                   stepg c {s,bool2bset b} {t,a} c'
                /\ bset2bool a b' /\ c1=-{b'}-c')
                \/ (exists c', exists a, exists bg, exists b',
                   step c {s,bg} {t,a} c' /\ introglitch (bool2bset b) bg
                /\ bset2bool a b' /\ c1=-{b'}-c').
Proof.
introv H. Inverts H.
- left. exists c' a b'. easy.
- right. exists c' a bg b'. easy.
Qed.


Lemma inv_stepgId : forall S (s t:{|S|}) c,
                    stepg (ID) s t c -> t=s /\ c=ID.
Proof. introv H. Inverts H. easy. Qed.

Lemma inv_stepgFo : forall S (s:{|S|}) t c,
                    stepg (FORK) s t c -> fstS t=s /\ sndS t = s /\ c=FORK.
Proof. introv H. Inverts H. easy. Qed.

Lemma inv_stepgSw : forall S T (s:{|S#T|}) t c,
                    stepg (SWAP) s t c ->  fstS t= sndS s /\ sndS t = fstS s /\ c=SWAP.
Proof. introv H. Inverts H. easy. Qed.

Lemma inv_stepgLs : forall S T U (s:{|S#T#U|}) t c,
                   stepg (LSH) s t c ->fstS t=fstS (fstS s) /\ fstS (sndS t) = sndS (fstS s)
                                    /\ sndS (sndS t) = sndS s /\ c=LSH.
Proof. introv H. Inverts H. easy. Qed.

Lemma inv_stepgRs : forall S T U (s:{|S#(T#U)|}) t c,
                    stepg (RSH) s t c -> fstS (fstS t)=fstS s /\ sndS (fstS t)=fstS (sndS s)
                                    /\ sndS t=sndS (sndS s) /\ c=RSH.
Proof. introv H. Inverts H. easy. Qed.

(* Generic lemmas when the plug or gate is unknown *)
Lemma inv_stepPlug : forall S T p s t c,
                      step (@Cplug S T p) s t c -> redplug p s = t /\ c=Cplug p.
Proof. introv H. Inverts H. easy. Qed.

Lemma inv_stepGate : forall S T g s t c,
                     step (@Cgate S T g) s t c -> redgate g s = t  /\ c = Cgate g.
Proof. introv H. Inverts H. easy. Qed.

Lemma inv_stepgPlug : forall S T p s t c,
                      stepg (@Cplug S T p) s t c -> redplug p s = t /\ c=Cplug p.
Proof. introv H. Inverts H. split; constructor; easy. Qed.

Lemma inv_stepgGate : forall S T g s t c,
                     stepg (@Cgate S T g) s t c -> introglitch (redgate g s) t /\ c=Cgate g.
Proof. introv H. Inverts H. split; easy. Qed.

Lemma inv_buset : forall S T (x1 x2:{|S|}) (y1 y2:{|T|}),
                  {x1,y1} = {x2,y2} -> x1=x2 /\ y1=y2.
Proof. introv H. Inverts H. easy. Qed.

Lemma inv_pure_bset : forall S T (x:{|S|}) (y:{|T|}),
                      pure_bset {x,y} -> pure_bset x /\ pure_bset y.
Proof. introv H. Inverts H. easy. Qed.

Lemma inv_bset2b0 : forall x, bset2bool (~0) x -> x=false.
Proof. introv H. Inverts H. reflexivity. Qed.


Lemma inv_bset2b1 : forall x, bset2bool (~1) x -> x=true.
Proof. introv H. Inverts H. reflexivity. Qed.

(***********************************************************)
(** **  Basic reduction properties used in autorewrite     *)
(***********************************************************)

Lemma rew_seq : forall S T U (c1:circuit S T) (c2:circuit T U) s, redcomb (c1 -o- c2) s = redcomb c2 (redcomb c1 s).
Proof. easy. Qed.

Lemma rew_par : forall S T U V (c1:circuit S T) (c2:circuit U V) s1 s2,
                redcomb (-|c1,c2|-) {s1,s2} = {redcomb c1 s1, redcomb c2 s2}.
Proof. easy. Qed.

Lemma rew_id : forall S (s:{|S|}), redcomb (ID) s = s.
Proof. easy. Qed.

Lemma rew_fork : forall S (s:{|S|}), redcomb (FORK) s = {s,s}.
Proof. easy. Qed.

Lemma rew_swap : forall S T (s:{|S|}) (t:{|T|}), redcomb (SWAP) {s,t} = {t,s}.
Proof. easy. Qed.

Lemma rew_lsh : forall S T U (s:{|S|}) (t:{|T|}) (u:{|U|}), redcomb (LSH) {s,t,u} = {s,{t,u}}.
Proof. easy. Qed.

Lemma rew_rsh : forall S T U (s:{|S|}) (t:{|T|}) (u:{|U|}), redcomb (RSH) {s,{t,u}} = {s,t,u}.
Proof. easy. Qed.

Lemma rew_negS1 : negS (~1) = ~0.
Proof. easy. Qed.

Lemma rew_negS2 : negS (~0) = ~1.
Proof. easy. Qed.

Lemma rew_andS1 : forall s, andS {s,s} = s.
Proof. introv. Destruct_s s; destruct x; easy. Qed.

Lemma rew_andS2 : forall s, andS {~0,s} = ~0.
Proof. introv. Destruct_s s; destruct x; easy. Qed.

Lemma rew_andS3 : forall s, andS {s,~0} = ~0.
Proof. introv. Destruct_s s; destruct x; easy. Qed.

Lemma rew_andS4 : forall s, andS {~1,s} = s.
Proof. introv. Destruct_s s; destruct x; easy. Qed.

Lemma rew_andS5 : forall s, andS {s,~1} = s.
Proof. introv. Destruct_s s; destruct x; easy. Qed.

Lemma rew_orS1 : forall s, orS {s,s} = s.
Proof. introv. Destruct_s s; destruct x; easy. Qed.

Lemma rew_orS2 : forall s, orS {~1,s} = ~1.
Proof. introv. Destruct_s s; destruct x; easy. Qed.

Lemma rew_orS3 : forall s, orS {s,~1} = ~1.
Proof. introv. Destruct_s s; destruct x; easy. Qed.

Lemma rew_orS4 : forall s, orS {~0,s} = s.
Proof. introv. Destruct_s s; destruct x; easy. Qed.

Lemma rew_orS5 : forall s, orS {s,~0} = s.
Proof. introv. Destruct_s s; destruct x; easy. Qed.

(* ####################################################### *)
(** *               Some tactics                           *)
(* ####################################################### *)

(**              Keeping only H in the context             *)

Ltac revert_all_but H :=
  let ty := type of H in
  repeat
  match goal with
    | H1 : ?A |- _ =>
      match constr:(ty = A) with
        | ?X = ?X => fail 1
        |    _    => revert H1
      end
  end.

(**               Destructing buses                            *)
(* A lemma to avoid a direct use of dependent destruction      *)
Lemma destruct_buset : forall S T (s:{|S#T|}), exists s1, exists s2, s={s1,s2}.
Proof. introv. exists (fstS s). exists (sndS s). Destruct_s s. easy. Qed.

Ltac Dd_buset_all := repeat (match goal with [i: buset (Pbus _ _) |- _] =>
                              destruct (destruct_buset i) as [? [? ?]]; subst end).

(** destructing a single variable with a composed buset type *)

Ltac Dd_buset x :=  revert_all_but x; Dd_buset_all; intros.

(** Reducing circuits in the goal using constructors  *)

Ltac Redstep_G := repeat ((eapply Sseq || eapply Spar ||eapply Sloop || constructor); cbn).
Ltac RedstepG  := repeat ((eapply Sseq || eapply Spar ||eapply Sloop || constructor); eauto).


(** Reduction of step and stepg hypotheses using inversion theorems *)

Ltac Invstep_H := repeat match goal with
                  | [H: step (Cseq _ _) _ _ _ |- _]  => let X := fresh "b" in
                                                        apply inv_stepS in H; cbn in H;
                                                        destruct H as [? [? [X [? [? ?]]]]];
                                                        Dd_buset X; subst
                  | [H: step (Cpar _ _) _ _ _ |- _]  => apply inv_stepP in H; cbn in H;
                                                        destruct H as [? [? [? [? [? [? [? [? ?]]]]]]]];
                                                        subst
                  | [H: step (Cloop _ _) _ _ _ |- _] => apply inv_stepL in H; cbn in H;
                                                        destruct H as [? [? [? [? [? ?]]]]];
                                                        subst
                 | [H: step (Cgate _) _ _  _ |- _]   => apply inv_stepGate in H;
                                                        destruct H as [H ?]; subst

                  | [H: step (Cplug (Pid _)) _ _ _     |- _] => apply inv_stepId in H;
                                                                cbn in H;
                                                                destruct H as [? ?]; subst
                  | [H: step (Cplug (Fork _)) _ _ _    |- _] => apply inv_stepFo in H;
                                                                cbn in H;
                                                                destruct H as [? [? ?]]; subst
                  | [H: step (Cplug (Swap _ _)) _ _ _  |- _] => apply inv_stepSw in H;
                                                                cbn in H;
                                                                destruct H as [? [? ?]]; subst
                  | [H: step (Cplug (Lsh _ _ _)) _ _ _ |- _] => apply inv_stepLs in H;
                                                                cbn in H;
                                                                destruct H as [? [? [? ?]]]; subst
                  | [H: step (Cplug (Rsh _ _ _)) _ _ _ |- _] => apply inv_stepRs in H;
                                                                cbn in H;
                                                                destruct H as [? [? [? ?]]]; subst
                  | [H: step (Cplug _) _ _  _ |- _]   => apply inv_stepPlug in H;
                                                         destruct H as [H ?]; subst

                  | [H: stepg (Cseq _ _) _ _ _ |- _]
                    => let X := fresh "b" in
                          (apply inv_stepgS1 in H; [idtac| solve [repeat constructor]];
                           destruct H as [?[?[X[?[? ?]]]]]; Dd_buset X; subst)
                       || (apply inv_stepgS2 in H; [idtac| solve [repeat constructor]];
                           destruct H as [?[?[X[?[? ?]]]]]; Dd_buset X; subst)
                       || (apply inv_stepgS in H; cbn in H;
                           destruct H as [[? [? [X [? [? ?]]]]] | [? [? [X [? [? ?]]]]]];
                           Dd_buset X; subst)
                  | [H: stepg (Cpar _ _) _ _ _ |- _]
                     => let X2 := fresh "b" in
                        let X2 := fresh "b" in
                       (apply inv_stepgP1 in H; [idtac| solve [repeat constructor]];
                           destruct H as [?[?[X1[X2[?[?[?[? ?]]]]]]]];
                           Dd_buset X1; Dd_buset X2; subst)
                    || (apply inv_stepgP2 in H; [idtac| solve [repeat constructor]];
                           destruct H as [?[?[X1[X2[?[?[?[? ?]]]]]]]];
                           Dd_buset X1; Dd_buset X2; subst)
                    || (apply inv_stepgP in H; cbn in H;
                        destruct H as [ [? [? [? [? [? [? [? [? ?]]]]]]]]
                                      | [? [? [? [? [? [? [? [? ?]]]]]]]]]; subst)

                  | [H: stepg (Cloop _ _) _ _ _ |- _] => apply inv_stepgL in H; cbn in H;
                                                         destruct H as [[? [? [? [? [? ?]]]]]
                                                                      | [? [? [? [?[? [? [? ?]]]]]]]];
                                                         subst
                  | [H: stepg (Cgate _) _ _  _ |- _]   => apply inv_stepgGate in H;
                                                          destruct H as [H ?]; subst
                  | [H: stepg (Cplug (Pid _)) _ _ _     |- _] => apply inv_stepgId in H;
                                                                 cbn in H;
                                                                 destruct H as [? ?]; subst
                  | [H: stepg (Cplug (Fork _)) _ _ _    |- _] => apply inv_stepgFo in H;
                                                                 cbn in H;
                                                                 destruct H as [? [? ?]]; subst
                  | [H: stepg (Cplug (Swap _ _)) _ _ _  |- _] => apply inv_stepgSw in H;
                                                                 cbn in H;
                                                                 destruct H as [? [? ?]]; subst
                  | [H: stepg (Cplug (Lsh _ _ _)) _ _ _ |- _] => apply inv_stepgLs in H;
                                                                 cbn in H;
                                                                 destruct H as [? [? [? ?]]]; subst
                  | [H: stepg (Cplug (Rsh _ _ _)) _ _ _ |- _] => apply inv_stepgRs in H;
                                                                 cbn in H;
                                                                 destruct H as [? [? [? ?]]]; subst
                 | [H: step (Cplug _) _ _  _ |- _]   => apply inv_stepgPlug in H;
                                                        destruct H as [H ?]; subst
                  end.


Ltac  Invstep H := revert_all_but H; Invstep_H; try subst; cbn in * |-; intros.

(* Reduction by rewriting  *)

Hint Rewrite rew_seq rew_par rew_id rew_fork rew_swap rew_lsh rew_rsh
             rew_negS1 rew_negS2
             rew_andS1 rew_andS2 rew_andS3 rew_andS4 rew_andS5
             rew_orS1 rew_orS2 rew_orS3 rew_orS4 rew_orS5: Rew_Combinatory.

Hint Rewrite rew_negS1 rew_negS2
             rew_andS1 rew_andS2 rew_andS3 rew_andS4 rew_andS5
             rew_orS1 rew_orS2 rew_orS3 rew_orS4 rew_orS5: Rew_Gates.


(** Infering fact about unchanged code for combinatorial circuits *)

Ltac Combcode H := match type of H with
                   | step _ _ _ _ => let X := fresh "C" in
                                     dupl H X; eapply step_comb_cir in X;
                                     [ idtac | repeat constructor ] ; subst
                   | stepg _ _ _ _ => let X := fresh "C" in
                                     dupl H X; eapply stepg_comb_cir in X;
                                     [ idtac | repeat constructor ] ; subst
                   end.



Ltac Rcomb :=
     repeat match goal with
     | [H: step ?C1 _ _ ?C2 |- _]  => try (let X := fresh "C" in
                                             dupl H X; eapply step_comb_cir in X;
                                             [ idtac | solve [repeat constructor] ] ; subst); revert H
     | [H: stepg ?C1 _ _ ?C2 |- _] => try (let X := fresh "C" in
                                             dupl H X; eapply stepg_comb_cir in X;
                                             [ idtac | solve [repeat constructor] ] ; subst); revert H
     end; intros.

(** Try to prove goals of the form pure-bset X  *)

Ltac Checkpure := try repeat constructor; try easy; try apply b2t_is_pure.
Ltac CheckPure := solve [try repeat constructor; try easy; try apply b2t_is_pure].

Ltac Rpure :=
     repeat match goal with
     | [H: step _ _ ?t _ |- _]  => match goal with
                                   | [H : pure_bset t |- _]   => fail 1
                                   | _ => let X := fresh "P" in
                                          dupl H X; eapply step_pure in X;
                                          [idtac | CheckPure]
                                   end
      end.


(** Using determinism of bset2bool to generate equalities    *)

Ltac Detbset2bool_tac H H1 := eapply det_bset2bool in H1; try (exact H); try easy; subst.

Tactic Notation "Detbset2bool" hyp(H1) hyp(H2) := Detbset2bool_tac H1 H2.
Tactic Notation "Detbset2bool" hyp(H1) hyp(H2) hyp(H3) := Detbset2bool H1 H2; Detbset2bool H1 H3.
Tactic Notation "Detbset2bool" hyp(H1) hyp(H2) hyp(H3) hyp(H4) := Detbset2bool H1 H2 H3; Detbset2bool H1 H4.


(** Using determinism of semgate to generate equalities    *)

Ltac Detgate_tac H H1 := eapply det_semgate in H1; try (exact H); subst.

Tactic Notation "Detsemgate" hyp(H1) hyp(H2) := Detgate_tac H1 H2.
Tactic Notation "Detsemgate" hyp(H1) hyp(H2) hyp(H3) := Detsemgate H1 H2; Detsemgate H1 H3.
Tactic Notation "Detsemgate" hyp(H1) hyp(H2) hyp(H3) hyp(H4) := Detsemgate H1 H2 H3; Detsemgate H1 H4.


(** Using determinism of step to generate equalities    *)
(*
Ltac Detstep_tac H H1 := eapply det_step in H1; try (exact H); try easy;
                         try (repeat constructor; try easy; try apply b2t_is_pure); destruct H1; subst.
*)
Ltac Detstep_tac H H1 := eapply det_step in H1; try (exact H);
                        [idtac | Checkpure]; destruct H1; subst.

Tactic Notation "Detstep" hyp(H1) hyp(H2) := Detstep_tac H1 H2.
Tactic Notation "Detstep" hyp(H1) hyp(H2) hyp(H3) := Detstep H1 H2; Detstep H1 H3.
Tactic Notation "Detstep" hyp(H1) hyp(H2) hyp(H3) hyp(H4) := Detstep H1 H2 H3; Detstep H1 H4.

Ltac Detstepres_tac H H1 := eapply det_step_res in H1; try (exact H); try easy; subst; subst.

Tactic Notation "Detstepres" hyp(H1) hyp(H2) := Detstepres_tac H1 H2.
Tactic Notation "Detstepres" hyp(H1) hyp(H2) hyp(H3) := Detstepres H1 H2; Detstepres H1 H3.
Tactic Notation "Detstepres" hyp(H1) hyp(H2) hyp(H3) hyp(H4) := Detstepres H1 H2 H3; Detstepres H1 H4.


Ltac Rdet :=
     repeat match goal with
   | [H: step ?C ?s ?t1 _, H1:step ?C ?s ?t2 _ |- _]  => (Detstep H H1)
                                                      || let X := fresh "D" in
                                                         dupl H1 X;
                                                         eapply det_step_res in X; [idtac | exact H];
                                                         subst; revert H1
     end; intros.


(** Prevervation if purity by semgate and step   *)

Ltac Purestep_tac H := let X := fresh "P" in
                       dupl H X; eapply step_pure in X;
                       [idtac | Checkpure].
Tactic Notation "Purestep" hyp(H1) := Purestep_tac H1.
Tactic Notation "Purestep" hyp(H1) hyp(H2) := Purestep_tac H1; Purestep_tac H2.
Tactic Notation "Purestep" hyp(H1) hyp(H2) hyp(H3) := Purestep_tac H1; Purestep_tac H2; Purestep_tac H3.

(* Basic simplification step : simplifies, destruct, clear hypotheses*)

Ltac SimpS :=
repeat match goal with
    | [i: buset (Pbus _ _) |- _]  => destruct (destruct_buset i) as [? [? ?]]; try subst
    | [H: {_,_}={_,_} |- _]       => apply inv_buset in H; destruct H as [? ?]; try subst
    | [H:context[sndS{_,_}] |- _] => simpl in H
    | [H:context[fstS{_,_}] |- _] => simpl in H
    | [H:context[snd(_,_)] |- _]  => simpl in H
    | [H:context[fst(_,_)] |- _]  => simpl in H
    | [H: pure_bset {_, _} |- _]  => apply inv_pure_bset in H; destruct H as [? ?]
    | [H: bset2bool (bool2bset _) _  |- _] => apply s2bob2s in H; try subst
    | [H: bset2bool (~1) _ |- _]  => apply inv_bset2b1 in H; try subst
    | [H: bset2bool (~0) _ |- _]  => apply inv_bset2b0 in H; try subst
    | [H: bset2bool ?x _ , H1:bset2bool ?x _ |- _]
       => eapply det_bset2bool in H1; [idtac|CheckPure|exact H]; try subst
    | [H: bool2bset _ = bool2bset _ |- _] => apply bool2bset_eq in H; try subst
    | [H: _ /\ _  |- _]     => destruct H; try subst
    | [H: ex _ |- _]        => destruct H; try subst
    | [H: ?x = ?x |- _]     => clear H
    | [H1: ?p, H2: ?p |- _] => clear H2
    end; subst.


(* Simplification with combines several tactics to infer new properties
 (combinational circuits, purity, by determinism)  *)

Ltac Simpl := Rcomb; Rpure; Rdet; SimpS; try eauto.


(* An apply with hypotheses which also tries to solve subgoals with CheckPure and easy *)
Tactic Notation "Apply" constr(E) :=
       eapply E; try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with" hyp(H0) :=
       eapply E; try exact H0; try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with" hyp(H0) hyp(H1) :=
       eapply E; try exact H0; try exact H1; try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with" hyp(H0) hyp(H1) hyp(H2) :=
       eapply E; try exact H0; try exact H1; try exact H2; try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with"
                hyp(H0) hyp(H1) hyp(H2) hyp(H3) :=
       eapply E; try exact H0; try exact H1; try exact H2; try exact H3;
                      try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with"
                hyp(H0) hyp(H1) hyp(H2) hyp(H3) hyp(H4) :=
       eapply E; try exact H0; try exact H1; try exact H2; try exact H3;
                 try exact H4; try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with"
                hyp(H0) hyp(H1) hyp(H2) hyp(H3) hyp(H4)
                hyp(H5) :=
       eapply E; try exact H0; try exact H1; try exact H2; try exact H3;
                 try exact H4; try exact H5; try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with"
                hyp(H0) hyp(H1) hyp(H2) hyp(H3) hyp(H4)
                hyp(H5) hyp(H6) :=
       eapply E; try exact H0; try exact H1; try exact H2; try exact H3;
                 try exact H4; try exact H5; try exact H6;
                 try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with"
                hyp(H0) hyp(H1) hyp(H2) hyp(H3) hyp(H4)
                hyp(H5) hyp(H6) hyp(H7) :=
       eapply E; try exact H0; try exact H1; try exact H2; try exact H3;
                 try exact H4; try exact H5; try exact H6; try exact H7;
                 try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with"
                hyp(H0) hyp(H1) hyp(H2) hyp(H3) hyp(H4)
                hyp(H5) hyp(H6) hyp(H7) hyp(H8) :=
       eapply E; try exact H0; try exact H1; try exact H2; try exact H3;
                 try exact H4; try exact H5; try exact H6; try exact H7;
                 try exact H8; try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with"
                hyp(H0) hyp(H1) hyp(H2) hyp(H3) hyp(H4)
                hyp(H5) hyp(H6) hyp(H7)  hyp(H8) hyp(H9) :=
       eapply E; try exact H0; try exact H1; try exact H2; try exact H3;
                 try exact H4; try exact H5; try exact H6; try exact H7;
                 try exact H8; try exact H9; try CheckPure; try easy.


Tactic Notation "Apply" constr(E) "in" hyp(H) :=
       eapply E in H; try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with" hyp(H0) "in" hyp(H) :=
       eapply E in H; try exact H0; try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with" hyp(H0) hyp(H1) "in" hyp(H) :=
       eapply E in H; try exact H0; try exact H1; try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with" hyp(H0) hyp(H1) hyp(H2) "in" hyp(H) :=
       eapply E in H; try exact H0; try exact H1; try exact H2; try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with"
                hyp(H0) hyp(H1) hyp(H2) hyp(H3)
                "in" hyp(H) :=
       eapply E in H; try exact H0; try exact H1; try exact H2; try exact H3;
                      try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with"
                hyp(H0) hyp(H1) hyp(H2) hyp(H3) hyp(H4)
                "in" hyp(H) :=
       eapply E in H; try exact H0; try exact H1; try exact H2; try exact H3;
                      try exact H4; try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with"
                hyp(H0) hyp(H1) hyp(H2) hyp(H3) hyp(H4)
                hyp(H5) "in" hyp(H) :=
       eapply E in H; try exact H0; try exact H1; try exact H2; try exact H3;
                      try exact H4; try exact H5; try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with"
                hyp(H0) hyp(H1) hyp(H2) hyp(H3) hyp(H4)
                hyp(H5) hyp(H6)
                "in" hyp(H) :=
       eapply E in H; try exact H0; try exact H1; try exact H2; try exact H3;
                      try exact H4; try exact H5; try exact H6;
                      try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with"
                hyp(H0) hyp(H1) hyp(H2) hyp(H3) hyp(H4)
                hyp(H5) hyp(H6) hyp(H7)
                "in" hyp(H) :=
       eapply E in H; try exact H0; try exact H1; try exact H2; try exact H3;
                      try exact H4; try exact H5; try exact H6; try exact H7;
                      try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with"
                hyp(H0) hyp(H1) hyp(H2) hyp(H3) hyp(H4)
                hyp(H5) hyp(H6) hyp(H7) hyp(H8)
                "in" hyp(H) :=
       eapply E in H; try exact H0; try exact H1; try exact H2; try exact H3;
                      try exact H4; try exact H5; try exact H6; try exact H7;
                      try exact H8; try CheckPure; try easy.
Tactic Notation "Apply" constr(E) "with"
                hyp(H0) hyp(H1) hyp(H2) hyp(H3) hyp(H4)
                hyp(H5) hyp(H6) hyp(H7)  hyp(H8) hyp(H9)
                "in" hyp(H) :=
       eapply E in H; try exact H0; try exact H1; try exact H2; try exact H3;
                      try exact H4; try exact H5; try exact H6; try exact H7;
                      try exact H8; try exact H9; try CheckPure; try easy.


