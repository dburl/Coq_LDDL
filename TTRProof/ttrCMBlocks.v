(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The triple modular redundancy transformation   
#</h1>#    
-   Lemmas on sub-circuits (control and memory block)
    used in ttr transformation  

              Pascal Fradet - Inria - 2014  
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)
Add LoadPath "..\Common\".
Require Export ttrDef.

Set Implicit Arguments.


(* ####################################################### *)
(**       Basic properties of the control block (cb_ttr)   *)
(* ####################################################### *)


Lemma fact_step_cb_ttrb : forall b (b1 b2: bool) t c,
                          step (cb_ttrb b1 b1 b2 b2 b2) b t c
                        -> let b3 := negb (orb b1 b2) in
                           t= {bool2bset b3,bool2bset b3,bool2bset b3}
                        /\ c = cb_ttrb b3 b3 b1 b1 b1.
Proof.
introv H. 
assert (F:fstep (cb_ttrb b1 b1 b2 b2 b2) b
              = Some ({bool2bset(negb (orb b1 b2)),bool2bset(negb (orb b1 b2)),bool2bset(negb(orb b1 b2))},
                      cb_ttrb (negb (orb b1 b2)) (negb (orb b1 b2)) b1 b1 b1))
   by (Destruct_s b; destruct x; destruct b1; destruct b2; vm_compute; easy).
Apply fstep_imp_detstep with H in F. SimpS. easy. 
Qed.

Lemma fact_step_cb0i : forall b t c, step (cb_ttrb false false false false false) b t c 
                                   -> t={~1,~1,~1} /\ c=(cb_ttrb true true false false false).
Proof.
introv H. apply fact_step_cb_ttrb in H. SimpS. easy. 
Qed.

Lemma fact_step_cb1i : forall b t c, step (cb_ttrb true true false false false) b t c 
                                   -> t={~0,~0,~0} /\ c=(cb_ttrb false false true true true).
Proof.
introv H. apply fact_step_cb_ttrb in H. SimpS. easy. 
Qed.

Lemma fact_step_cb2i : forall b t c, step (cb_ttrb false false true true true) b t c 
                                   ->  t={~0,~0,~0} /\ c=(cb_ttrb false false false false false).
Proof.
introv H. apply fact_step_cb_ttrb in H. SimpS. easy. 
Qed.

Lemma fact_step_ccb : forall (b1 b2 b3 b4 b5 b6 a1 a2: bool) t c,
                          step (cb_ttrb b2 b3 b4 b5 b6) (bool2bset b1) t c
                       -> ccb a1 a2 b1 b2 b3 b4 b5 b6
                       -> let o := negb (orb a1 a2) in
                           t= {bool2bset o,bool2bset o,bool2bset o}
                        /\ c = cb_ttrb o o a1 a1 a1.
Proof.
introv H G. Inverts G. 
- assert (F:fstep (cb_ttrb b3 b3 b6 b6 b6) (bool2bset b1)
              = Some ({bool2bset (negb (b3 || b6)), bool2bset (negb (b3 || b6)),
                       bool2bset (negb (b3 || b6))}, cb_ttrb (negb (b3 || b6)) (negb (b3 || b6)) b3 b3 b3))
   by (destruct b1; destruct b3; destruct b6; vm_compute; easy).
  eapply fstep_imp_detstep in F; Simpl.
- assert (F:fstep (cb_ttrb b2 b3 b6 b6 b6) (bool2bset b3)
              = Some ({bool2bset (negb (b3 || b6)), bool2bset (negb (b3 || b6)),
                       bool2bset (negb (b3 || b6))},cb_ttrb (negb (b3 || b6)) (negb (b3 || b6)) b3 b3 b3))
   by (destruct b2; destruct b3; destruct b6; vm_compute; easy).
  eapply fstep_imp_detstep in F; Simpl. 
- assert (F:fstep  (cb_ttrb b2 b3 b6 b6 b6) (bool2bset b2)
              = Some ({bool2bset (negb (b2 || b6)), bool2bset (negb (b2 || b6)),
                       bool2bset (negb (b2 || b6))},cb_ttrb (negb (b2 || b6)) (negb (b2 || b6)) b2 b2 b2))
   by (destruct b2; destruct b3; destruct b6; vm_compute; easy).
  eapply fstep_imp_detstep in F; Simpl.
- assert (F:fstep (cb_ttrb b3 b3 b4 b6 b6) (bool2bset b3) 
              = Some ({bool2bset (negb (b3 || b6)), bool2bset (negb (b3 || b6)),
                       bool2bset (negb (b3 || b6))},cb_ttrb (negb (b3 || b6)) (negb (b3 || b6)) b3 b3 b3))
   by (destruct b3; destruct b4; destruct b6; vm_compute; easy).
  eapply fstep_imp_detstep in F; Simpl.
- assert (F:fstep (cb_ttrb b3 b3 b6 b5 b6) (bool2bset b3)
              = Some ({bool2bset (negb (b3 || b6)), bool2bset (negb (b3 || b6)),
                       bool2bset (negb (b3 || b6))},cb_ttrb (negb (b3 || b6)) (negb (b3 || b6)) b3 b3 b3))
   by (destruct b3; destruct b5; destruct b6; vm_compute; easy).
  eapply fstep_imp_detstep in F; Simpl.
- assert (F:fstep (cb_ttrb b3 b3 b5 b5 b6) (bool2bset b3)
              = Some ({bool2bset (negb (b3 || b5)), bool2bset (negb (b3 || b5)),
                       bool2bset (negb (b3 || b5))},cb_ttrb (negb (b3 || b5)) (negb (b3 || b5)) b3 b3 b3))
   by (destruct b3; destruct b5; destruct b6; vm_compute; easy).
  eapply fstep_imp_detstep in F; Simpl. 
Qed.

Lemma fact_step_ccb0 : forall b1 b2 b3 b4 b5 b6 t c, 
                        step (cb_ttrb b2 b3 b4 b5 b6) (bool2bset b1) t c
                     -> ccb false false b1 b2 b3 b4 b5 b6
                     -> c=(cb_ttrb true true false false false)
                     /\ t={~1,~1,~1}.
Proof.
introv H C.
apply fact_step_ccb with (a1:=false) (a2:=false) in H; SimpS; easy.
Qed.

Lemma fact_step_ccb1 : forall b1 b2 b3 b4 b5 b6 t c, 
                        step (cb_ttrb b2 b3 b4 b5 b6) (bool2bset b1) t c
                     -> ccb true false b1 b2 b3 b4 b5 b6
                     -> c=(cb_ttrb false false true true true)
                     /\ t={~0,~0,~0}.
Proof.
introv H C.
apply fact_step_ccb with (a1:=true) (a2:=false) in H; SimpS; easy.
Qed.

Lemma fact_step_ccb2 : forall b1 b2 b3 b4 b5 b6 t c, 
                        step (cb_ttrb b2 b3 b4 b5 b6) (bool2bset b1) t c
                     -> ccb false true b1 b2 b3 b4 b5 b6
                     -> c=(cb_ttrb false false false false false)
                     /\  t={~0,~0,~0}.
Proof.
introv H C.
apply fact_step_ccb with (a1:=false) (a2:=true) in H; SimpS; easy.
Qed.


Lemma fact_step_ncb0 : forall S s x cb , step (cb_ttr S) s x cb -> x={s,{~1,~1}} /\ cb = (cb_ttr1 S). 
Proof.
introv H. unfold cb_ttr in H. Invstep H.
apply fact_step_cb0i in H2. SimpS. easy.
Qed.

Lemma fact_step_ncb1 : forall S s x cb , step (cb_ttr1 S) s x cb -> x={s,{~0,~0}} /\ cb = (cb_ttr2 S). 
Proof.
introv H. unfold cb_ttr1 in H. Invstep H.
apply fact_step_cb1i in H2. SimpS. easy. 
Qed.

Lemma fact_step_ncb2 : forall S s x cb , step (cb_ttr2 S) s x cb -> x={s,{~0,~0}} /\ cb = (cb_ttr S). 
Proof.
introv H. unfold cb_ttr2 in H. Invstep H.
apply fact_step_cb2i in H2. SimpS. easy. 
Qed.


(* ####################################################### *)
(**         Basic Properties of the memory block           *)
(* ####################################################### *)

Lemma fact0_mb_ttr: forall a b c d f x y z t m, 
                     step (mb_ttr a b c d) {x,{y,z}} {t,f} m 
                  -> f={y,z}.
Proof.
introv H.
unfold mb_ttr in H. unfold DUPL in H. 
Invstep H. SimpS. easy.
Qed.

Lemma fact_stepg_mb : forall a b c d f f' s t m, 
                      stepg (mb_ttr a b c d) {s,f} {t,f'} m 
                   -> f=f'.
Proof.
introv H.
unfold mb_ttr in H. unfold DUPL in H.
Invstep H; SimpS; easy. 
Qed.

Lemma step0_mb_ttr1: forall b x y m t c, 
                     step (mb_ttr b b x y) {m,{~1, ~ 1}} t c 
                  -> t={bool2bset b, {~ 1, ~1}} /\ exists b', bset2bool m b' /\ c=mb_ttr b' b b b.
Proof.
introv H.
unfold mb_ttr in H. unfold dl_ttr in H. unfold DUPL in H. Invstep H. 
assert (F:fstep (voting_ttr x17 y) {m, {bool2bset x33, bool2bset x33}, {~ 1, ~ 1}} 
              = Some (bool2bset x33,voting_ttr x33 x33)) 
       by (Destruct_s m; destruct x; destruct x17; destruct x33; cbv; easy).
Dd_buset t.
Apply fstep_imp_detstep in F; try exact H3; Simpl; Simpl.
Qed.

Lemma step0_mb_ttr2: forall b x y z t c, 
                     step (mb_ttr x b y z) {bool2bset b,{~1, ~ 1}} t c 
                  -> t={bool2bset b, {~ 1, ~1}} /\ c=mb_ttr b x b b.
Proof.
introv H.
assert (F:fstep (mb_ttr x b y z) {bool2bset b,{~1,~1}} = Some ({bool2bset b, {~1,~1}},mb_ttr b x b b)). 
destruct b; destruct x; destruct y; destruct z; cbv; easy.
eapply fstep_imp_detstep in F; Simpl. 
Qed.


Lemma step0_mb_ttr3: forall b x y z t c, 
                     step (mb_ttr b x y z) {bool2bset b,{~1, ~ 1}} t c 
                  -> t={bool2bset b, {~ 1, ~1}} /\ c=mb_ttr b b b b.
Proof.
introv H.
assert (F:fstep (mb_ttr b x y z) {bool2bset b,{~1,~1}} = Some ({bool2bset b, {~1,~1}},mb_ttr b b b b)). 
destruct b; destruct x; destruct y; destruct z; cbv; easy.
eapply fstep_imp_detstep in F; Simpl. 
Qed.


Lemma step0_mb_ttr4: forall b x fA t c, 
                     step (mb_ttr b b x x) {bool2bset b,{fA, ~ 1}} t c
                  -> t={bool2bset b, {fA, ~1}} /\ (c=mb_ttr b b b b).
Proof.
introv H.
assert (F:fstep (mb_ttr b b x x) {bool2bset b,{fA, ~ 1}} = Some ({bool2bset b, {fA, ~1}},mb_ttr b b b b))
    by (destruct b; destruct x; Destruct_s fA; destruct x; cbv; easy).
eapply fstep_imp_detstep in F; Simpl.
Qed.

Lemma step0_mb_ttr5: forall b x fB t c, 
                     step (mb_ttr b b x x) {bool2bset b, {~ 1, fB}} t c
                   -> t={bool2bset b, {~ 1, fB}} /\ (c=mb_ttr b b b b).
Proof.
introv H.
assert (F:fstep (mb_ttr b b x x) {bool2bset b, {~ 1, fB}} = Some ({bool2bset b, {~1,fB}},mb_ttr b b b b))
    by (destruct b; destruct x; Destruct_s fB; destruct x; cbv; easy).
eapply fstep_imp_detstep in F; Simpl.
Qed.

Lemma step1_mb_ttr1: forall b b1 b2 x c t, 
                     step (mb_ttr b1 b2 b b) {x,{~0,~0}} t c 
                  -> t={bool2bset b, {~0,~0}} /\ exists b3, bset2bool x b3 /\ c=mb_ttr b3 b1 b b.
Proof.
introv H. Dd_buset t.
unfold mb_ttr in H. unfold dl_ttr in H. unfold DUPL in H. Invstep H. 
assert (F:fstep (voting_ttr b b) {x19, {bool2bset x36, bool2bset b2}, {~0,~0}}
              = Some (bool2bset b,voting_ttr b b))
by (Destruct_s x19; destruct x; destruct b; destruct b2; vm_compute; easy). 
eapply fstep_imp_detstep in F; Simpl. Simpl. 
Qed.


Lemma step1_mb_ttr3: forall b b1 x z c t, 
                     step (mb_ttr b1 b b z) {x,{~0,~0}} t c 
                  -> t={bool2bset b, {~0,~0}} /\ exists b3, bset2bool x b3 /\ c=mb_ttr b3 b1 b b.
Proof.
introv H. Dd_buset t.
unfold mb_ttr in H. unfold dl_ttr in H. unfold DUPL in H. Invstep H. 
assert (F:fstep (voting_ttr b z) {x19, {bool2bset x36, bool2bset b}, {~ 0, ~ 0}}
              = Some (bool2bset b,voting_ttr b b))
by (Destruct_s x19; destruct x; destruct b; destruct x36; destruct z; vm_compute; easy). 
eapply fstep_imp_detstep in F; Simpl. Simpl. 
Qed.

Lemma step1_mb_ttr4: forall b d2 x fA c t, 
                     step (mb_ttr d2 b b b) {x,{fA,~0}} t c 
                  -> t={bool2bset b, {fA,~0}} /\ exists b', bset2bool x b' /\ c=mb_ttr b' d2 b b.
Proof.
introv H. Dd_buset t.
unfold mb_ttr in H. unfold dl_ttr in H. unfold DUPL in H. Invstep H. 
assert (F:fstep (voting_ttr b b) {x19, {bool2bset x36, bool2bset b}, {fA,~0}}
              = Some (bool2bset b,voting_ttr b b))
by (Destruct_s x19; destruct x; Destruct_s fA; destruct x; 
    destruct b; destruct x36; vm_compute; easy). 
eapply fstep_imp_detstep in F; Simpl. Simpl. 
Qed.

Lemma step1_mb_ttr5: forall b d2 x fB c t, 
                     step (mb_ttr d2 b b b) {x,{~0,fB}} t c 
                  -> t={bool2bset b, {~0,fB}} /\ exists b', bset2bool x b' /\ c=mb_ttr b' d2 b b.
Proof.
introv H. Dd_buset t.
unfold mb_ttr in H. unfold dl_ttr in H. unfold DUPL in H. Invstep H. 
assert (F:fstep (voting_ttr b b) {x19, {bool2bset x36, bool2bset b}, {~ 0, fB}}
              = Some (bool2bset b,voting_ttr b b))
by (Destruct_s x19; destruct x; Destruct_s fB; destruct x; 
    destruct x36; destruct b; vm_compute; easy). 
eapply fstep_imp_detstep in F; Simpl. Simpl. 
Qed.


Lemma step1_mb_ttr6: forall b d1 d2 d3 t c, 
                     step (mb_ttr d2 d3 b b)  {bool2bset d1, {~0,~0}} t c
                   -> t={bool2bset b, {~0,~0}} /\ (c=mb_ttr d1 d2 b b).
Proof.
introv H.
assert (F:fstep (mb_ttr d2 d3 b b) {bool2bset d1, {~0,~0}} = Some ({bool2bset b,{~0,~0}},mb_ttr d1 d2 b b))
    by (destruct b; destruct d1; destruct d2; destruct d3; cbv; easy).
eapply fstep_imp_detstep in F; Simpl. 
Qed.

Lemma step2_mb_ttr1: forall b b1 b2 x c t, 
                     step (mb_ttr b1 b b2 b) {x,{~0,~0}} t c 
                  -> t={bool2bset b, {~0,~0}} /\ exists b3, bset2bool x b3 /\ c=mb_ttr b3 b1 b b.
Proof.
introv H. Dd_buset t.
unfold mb_ttr in H. unfold dl_ttr in H. unfold DUPL in H. Invstep H. 
assert (F:fstep (voting_ttr b2 b) {x19, {bool2bset x36, bool2bset b}, {~ 0, ~ 0}}
              = Some (bool2bset b,voting_ttr b b))
    by (Destruct_s x19; destruct x; destruct b; destruct b2; destruct x36; vm_compute; try easy). 
eapply fstep_imp_detstep in F; Simpl. Simpl. 
Qed.



(** Basic Properties of the (protected) control block      *)
(**  (by reflection)                                       *)

Lemma stepg_cb_ttrb0 : forall p t c, 
                       ((fun p => p=(~0)) p)
                     -> stepg ((fun _ => cb_ttrb false false false false false) p) 
                               ((fun _ =>(~0)) p) t c
                      -> (fun e => 
                         (snd e=(cb_ttrb true true false false false) 
                            /\ (snd(fst e)={~1,~1,~1} \/ (snd(fst e)={~?,~1,~?} \/ (snd(fst e)={~1,~?,~1}))))
                      \/ (snd(fst e)={~1,~1,~1} /\ (snd e=cb_ttrb false true false false false 
                                                  \/ snd e=cb_ttrb true false false false false 
                                                  \/ snd e=cb_ttrb true true true false false 
                                                  \/ snd e=cb_ttrb true true false true false 
                                                  \/ snd e=cb_ttrb true true false false true))
                      \/ ((snd(fst e)={~1,~?,~1} /\ snd e=cb_ttrb false true false false false))) (p,t,c).
Proof. introv. Reflo_step_g. Qed.

Lemma fact_stepg_cb0 : forall S s t c, stepg (cb_ttr S) s t c 
                                   ->  (t={s,{~1,~1}} \/ t={s,{~1,~?}} \/ t={s,{~?,~1}})
                                   /\ (exists b1 b2 b3 b4 b5 b6, c=(-{b1}--|ID,cb_ttrb b2 b3 b4 b5 b6|--o-RSH)
                                                              /\ ccb true false b1 b2 b3 b4 b5 b6).
Proof.
introv H. 
Dd_buset t.
unfold  cb_ttr in H.
 Invstep H; SimpS. 
- apply stepg_cb_ttrb0 with (p:=(~0)) in H1; Simpl. 
  destruct H1 as [[H1 [H2|[H2|H2]]] | [[H1 [H2|[H2|[H2|[H2|H2]]]]] | [? H2]]]; split; Simpl.
  + exists true true true false false false. easy.
  + Inverts H0. 
    * exists true true true false false false. easy.
    * exists false true true false false false. easy.
  + exists true true true false false false. easy.
  + exists true false true false false false. easy.
  + exists true true false false false false. easy.
  + exists true true true true false false. easy.
  + exists true true true false true false. easy.
  + exists true true true false false true.  easy.
  + exists true false true false false false. easy.
- apply fact_step_cb0i in H3. SimpS.
  Inverts H0; split; try easy.  
  + exists true true true false false false. easy.
  + exists true true true false false false. easy.
Qed.


(* ######################################################### *)
(* stepg_cb_ttrb1 : stepg (cb_ttrb false false false false false) (~0) t c
                      -> (c=(cb_ttrb true true false false false) 
                              /\ (t={~0,~0,~0} \/ t={~?,~0,~0} \/ t={~0,~?,~0} \/ t={~0,~0,~?}))
                      \/ (t={~0,~0,~0} /\ (c=cb_ttrb false true false false false 
                                        \/ c=cb_ttrb true false false false false 
                                        \/ c=cb_ttrb true true true false false 
                                        \/ c=cb_ttrb true true false true false 
                                        \/ c=cb_ttrb true true false false true)).  *)
Lemma stepg_cb_ttrb1 : forall p t c, 
                       ((fun p => p=(~1)) p)
                     -> stepg ((fun _ => cb_ttrb true true false false false) p) 
                               ((fun _ =>(~1)) p) t c
                      -> (fun e =>
                         (snd e = cb_ttrb false false true true true 
                            /\ (snd(fst e)={~0,~0,~0} \/ snd(fst e)={~?,~0,~?} \/ snd(fst e)={~0,~?,~0}))
                      \/ (snd(fst e)={~0,~0,~0} /\ (snd e=cb_ttrb true false true true true
                                        \/ snd e=cb_ttrb false true true true true
                                        \/ snd e=cb_ttrb false false false true true
                                        \/ snd e=cb_ttrb false false true false true 
                                        \/ snd e=cb_ttrb false false true true false))
                      \/ (snd(fst e)={~0,~?,~0} /\ snd e=cb_ttrb true false true true true)) (p,t,c).
Proof. introv. Reflo_step_g. Qed.


Lemma fact_stepg_cb1 : forall S s t c, stepg (cb_ttr1 S) s t c 
                                   -> (t={s,{~0,~0}} \/ t={s,{~0,~?}} \/ t={s,{~?,~0}})
                                   /\ (exists b1 b2 b3 b4 b5 b6, c=(-{b1}--|ID,cb_ttrb b2 b3 b4 b5 b6|--o-RSH)
                                                              /\ ccb false true b1 b2 b3 b4 b5 b6).  
Proof.
introv H. Dd_buset t.
unfold cb_ttr1 in H.
Invstep H; SimpS.
- apply stepg_cb_ttrb1 with (p:=~1) in H1; Simpl. 
  destruct H1 as [[H1 [H2|[H2|H2]]] | [[H1 [H2|[H2|[H2|[H2|H2]]]]] | [? H2]]]; split; Simpl.
  + exists false false false true true true. easy.
  + Inverts H0. 
    * exists true false false true true true. easy.
    * exists false false false true true true. easy.
  + exists false false false true true true. easy.
  + exists false true false true true true. easy.
  + exists false false true true true true. easy.
  + exists false false false false true true. easy.
  + exists false false false true false true. easy.
  + exists false false false true true false. easy.
  + exists false true false true true true. easy.
- apply fact_step_cb1i in H3. SimpS.
  Inverts H0; split; try easy; exists false false false true true true; easy.
Qed.


(* ######################################################### *)
(* stepg_cb_ttrb1 : stepg (cb_ttrb false false false false false) (~0) t c
                      -> (c=(cb_ttrb true true false false false) 
                              /\ (t={~0,~0,~0} \/ t={~?,~0,~0} \/ t={~0,~?,~0} \/ t={~0,~0,~?}))
                      \/ (t={~0,~0,~0} /\ (c=cb_ttrb false true false false false 
                                        \/ c=cb_ttrb true false false false false 
                                        \/ c=cb_ttrb true true true false false 
                                        \/ c=cb_ttrb true true false true false 
                                        \/ c=cb_ttrb true true false false true)).  *)


Lemma stepg_cb_ttrb2 : forall p t c,
                        ((fun p => p=(~0)) p)
                      -> stepg ((fun _ => cb_ttrb false false true true true) p) 
                               ((fun _ =>(~0)) p) t c
                      -> (fun e => 
                                  (snd e=(cb_ttrb false false false false false) 
                                   /\  (snd(fst e)={~0,~0,~0} \/ snd(fst e)={~?,~0,~?} \/ snd(fst e)={~0,~?,~0}))
                            \/ (snd(fst e)={~0,~0,~0} /\ (snd e=cb_ttrb true false false false false 
                                        \/ snd e=cb_ttrb false true false false false
                                        \/ snd e=cb_ttrb false false true false false
                                        \/ snd e=cb_ttrb false false false true false
                                        \/ snd e=cb_ttrb false false false false true))
                           \/ (snd(fst e)={~0,~?,~0} /\ snd e=cb_ttrb true false false false false)) (p,t,c).

Proof. introv. Reflo_step_g. Qed.

Lemma fact_stepg_cb2 : forall S s t c, stepg (cb_ttr2 S) s t c 
                                  -> (t={s,{~0,~0}} \/ t={s,{~0,~?}} \/ t={s,{~?,~0}})
                                   /\ (exists b1 b2 b3 b4 b5 b6, c=(-{b1}--|ID,cb_ttrb b2 b3 b4 b5 b6|--o-RSH)
                                                                          /\ ccb false false b1 b2 b3 b4 b5 b6).
Proof.
introv H. Dd_buset t.
unfold cb_ttr2 in H.
Invstep H; SimpS. 
- apply stepg_cb_ttrb2 with (p:=~0) in H1; Simpl. 
  destruct H1 as [[H1 [H2|[H2|H2]]] | [[H1 [H2|[H2|[H2|[H2|H2]]]]] | [? H2]]]; split; Simpl.
  + exists false false false false false false. easy. 
  + Inverts H0. 
    * exists true false false false false false. easy. 
    * exists false false false false false false. easy. 
  + exists false false false false false false. easy.
  + exists false true false false false false. easy. 
  + exists false false true false false false. easy. 
  + exists false false false true false false. easy. 
  + exists false false false false true false. easy. 
  + exists false false false false false true. easy. 
  + exists false true false false false false. easy.
- apply fact_step_cb2i in H3. SimpS.
  Inverts H0; split; try easy; exists false false false false false false; easy.
Qed.

(** Basic Properties of the corruption of the memory block      *)
(** stepg properties (by reflection)                            *)


(** Prop : forall d k, stepg (mb_ttr (bset2bool d) (bset2bool d) k k) {d, {~1,~1}} t c 
                    -> t = {d,{~1,~1}} /\ ( c=  mb_ttr b b b x \/ c=  mb_ttr b x b b)
                                            \/ c=  mb_ttr x b b b)
                       \/ (sndS t = {~1,~1} /\ ( c=  mb_ttr b b x b)                  *)

Lemma stepg_mb_ttr0r : forall p t c, 
                       ((fun p => pure_bset p) p)
                    -> stepg ((fun p => mb_ttr (fbset2bool (fstS p)) (fbset2bool (fstS p))
                                               (fbset2bool (sndS p)) (fbset2bool (sndS p))) p) 
                               ((fun p => {fstS p, {~1,~1}}) p) t c
                -> (fun e => (exists x, (snd(fst e)={fstS(fst(fst e)),{~1,~1}}   
                                 /\ snd e =  mb_ttr (fbset2bool (fstS (fst(fst e)))) (fbset2bool (fstS (fst(fst e))))
                                                         (fbset2bool (fstS (fst(fst e)))) x)
                           \/ (snd(fst e)={fstS(fst(fst e)),{~1,~1}} 
                            /\ snd e =  mb_ttr (fbset2bool (fstS (fst(fst e)))) x 
                              (fbset2bool (fstS (fst(fst e)))) (fbset2bool (fstS (fst(fst e)))))
                           \/ (snd(fst e)={fstS(fst(fst e)),{~1,~1}} 
                              /\ snd e =  mb_ttr x (fbset2bool (fstS (fst(fst e)))) 
                                                   (fbset2bool (fstS (fst(fst e)))) (fbset2bool (fstS (fst(fst e)))))
                           \/ (sndS (snd(fst e))= {~1,~1} 
                            /\ snd e =  mb_ttr (fbset2bool (fstS (fst(fst e)))) (fbset2bool (fstS (fst(fst e))))
                                               x (fbset2bool (fstS (fst(fst e))))))) (p,t,c). 
Proof. introv. Reflo_step_g. Qed.


Lemma stepg_mb_ttr0 : forall d b x t c, 
                   pure_bset d -> bset2bool d b 
                -> stepg (mb_ttr b b x x) {d, {~1,~1}} t c
                -> (exists x,   t={d,{~1,~1}} /\ c=  mb_ttr b b b x)
                \/ (exists x,   t={d,{~1,~1}} /\ c=  mb_ttr b x b b)
                \/ (exists x,   t={d,{~1,~1}} /\ c=  mb_ttr x b b b)
                \/ (exists x, sndS t= {~1,~1} /\ c=  mb_ttr b b x b). 
Proof.
introv P B H.
set (p := {d,bool2bset x}).
Apply fbset2bool_equiv in B.
assert (X1: fbset2bool (fstS p) = b) 
    by (replace p with {d, bool2bset x}; try easy).
assert (X2: fbset2bool (sndS p) = x)
    by (replace p with {d, bool2bset x}; destruct x; try easy).
rewrite <- X1 in H.
rewrite <- X2 in H.
Apply stepg_mb_ttr0r in H.
simpl in H.
destruct H as [z [[H1 H2]|[[H1 H2]|[[H1 H2]|[H1 H2]]]]]; rewrite B in H2;
eauto; right; eauto.
Qed.


(*  p = {b,d} *)

Lemma stepg_mb_ttr1r : forall p t c, 
                       ((fun p => pure_bset p) p)
                    -> stepg ((fun p => mb_ttr (fbset2bool (fstS p)) (fbset2bool (fstS p))
                                               (fbset2bool (fstS p)) (fbset2bool (fstS p))) p) 
                               ((fun p => {sndS p, {~0,~0}}) p) t c
                   -> (fun e => (exists x, (snd (fst e)={fstS (fst(fst e)),{~0,~0}} 
                                          /\ snd e = mb_ttr (fbset2bool (sndS (fst(fst e))))
                                                            (fbset2bool (fstS (fst(fst e))))
                                                            (fbset2bool (fstS (fst(fst e)))) x)
                                      \/ (snd (fst e) ={fstS (fst(fst e)),{~0,~0}}  
                                          /\ snd e =  mb_ttr (fbset2bool (sndS (fst(fst e)))) x 
                                                             (fbset2bool (fstS (fst(fst e))))
                                                             (fbset2bool (fstS (fst(fst e)))))
                                      \/ (snd (fst e) ={fstS (fst(fst e)),{~0,~0}}  
                                          /\ snd e =  mb_ttr x (fbset2bool (fstS (fst(fst e))))
                                                               (fbset2bool (fstS (fst(fst e))))
                                                               (fbset2bool (fstS (fst(fst e)))))
                                      \/ (sndS (snd (fst e)) = {~0,~0} 
                                          /\ snd e = mb_ttr (fbset2bool (sndS (fst(fst e))))
                                                    (fbset2bool (fstS (fst(fst e)))) x 
                                                    (fbset2bool (fstS (fst(fst e))))))) (p,t,c).
Proof. introv. Reflo_step_g. Qed.


Lemma stepg_mb_ttr1 : forall d dd b bb  t c, 
                   pure_bset d -> pure_bset b -> bset2bool d dd -> bset2bool b bb
                -> stepg (mb_ttr bb bb bb bb) {d, {~0,~0}} t c
                -> (exists x,   t={b,{~0,~0}}  /\ c=  mb_ttr dd bb bb x)
                \/ (exists x,   t={b,{~0,~0}}  /\ c=  mb_ttr dd x bb bb)
                \/ (exists x,   t={b,{~0,~0}}  /\ c=  mb_ttr x bb bb bb)
                \/ (exists x, sndS t = {~0,~0} /\ c=  mb_ttr dd bb x bb). 
Proof.
introv P1 P2 B1 B2 H.
Apply fbset2bool_equiv in B1.
Apply fbset2bool_equiv in B2.
set (p := {b,d}).
assert (X1: fbset2bool (fstS p) = bb)
    by (replace p with {b,d}; try easy).
rewrite <- X1 in H.
replace d with (sndS p) in H; try easy.
Apply stepg_mb_ttr1r in H.
simpl in H. subst. 
destruct H as [z [[H1 H2]|[[H1 H2]|[[H1 H2]|[H1 H2]]]]]; eauto; right; eauto.
Qed.


(** Prop : forall b d, stepg (mb_ttr (bset2bool d) b b b) {d, {~0,~0}} t c 
                    -> t = {b,{~0,~0}} /\ (c=mb_ttr (bset2bool d) (bset2bool d) b x
                                                  \/ c=mb_ttr (bset2bool d) x b b)
                                                  \/ c=mb_ttr x (bset2bool d) b b)
                       \/ (sndS t={~1,~1} /\ (c=mb_ttr (bset2bool d) (bset2boold) x b)            *)
(*  p = {b,d} *)

Lemma stepg_mb_ttr2r : forall p t c, 
                      ((fun p => pure_bset p) p)
                    -> stepg ((fun p => mb_ttr (fbset2bool (sndS p)) (fbset2bool (fstS p))
                                               (fbset2bool (fstS p)) (fbset2bool (fstS p))) p) 
                               ((fun p => {sndS p, {~0,~0}}) p) t c
                   -> (fun e => 
                       (exists x, (snd (fst e) = {fstS (fst(fst e)),{~0,~0}} 
                                    /\ snd e = mb_ttr (fbset2bool (sndS (fst(fst e))))
                                                   (fbset2bool (sndS (fst(fst e))))
                                                    (fbset2bool (fstS (fst(fst e)))) x)
                           \/ (snd (fst e)={fstS (fst(fst e)),{~0,~0}} 
                                    /\ snd e = mb_ttr (fbset2bool (sndS (fst(fst e)))) x 
                                                   (fbset2bool (fstS (fst(fst e))))
                                                   (fbset2bool (fstS (fst(fst e)))))
                           \/ (snd (fst e)={fstS (fst(fst e)),{~0,~0}}  
                                    /\ snd e = mb_ttr x (fbset2bool (sndS (fst(fst e))))
                                                     (fbset2bool (fstS (fst(fst e))))
                                                     (fbset2bool (fstS (fst(fst e)))))
                           \/ (sndS (snd (fst e)) = {~0,~0} 
                                   /\ snd e = mb_ttr (fbset2bool (sndS (fst(fst e))))
                                                     (fbset2bool (sndS (fst(fst e)))) x
                                                     (fbset2bool (fstS (fst(fst e))))))) (p,t,c). 
Proof. introv. Reflo_step_g. Qed.


Lemma stepg_mb_ttr2 : forall d dd b bb  t c, 
                   pure_bset d -> pure_bset b -> bset2bool d dd -> bset2bool b bb
                -> stepg (mb_ttr dd bb bb bb) {d, {~0,~0}} t c
                -> (exists x,   t={b,{~0,~0}}  /\ c=  mb_ttr dd dd bb x)
                \/ (exists x,   t={b,{~0,~0}}  /\ c=  mb_ttr dd x bb bb)
                \/ (exists x,   t={b,{~0,~0}}  /\ c=  mb_ttr x dd bb bb)
                \/ (exists x, sndS t = {~0,~0} /\ c=  mb_ttr dd dd x bb). 
Proof.
introv P1 P2 B1 B2 H.
Apply fbset2bool_equiv in B1.
Apply fbset2bool_equiv in B2.
set (p := {b,d}).
assert (X1: fbset2bool (fstS p) = bb)
    by (replace p with {b,d}; try easy).
assert (X2: fbset2bool (sndS p) = dd)
    by (replace p with {b,d}; try easy).
rewrite <- X1 in H. rewrite <- X2 in H.
replace d with (sndS p) in H; try easy.
Apply stepg_mb_ttr2r in H.
simpl in H. subst. 
destruct H as [z [[H1 H2]|[[H1 H2]|[[H1 H2]|[H1 H2]]]]]; eauto;  
right; eauto.
Qed.
