
(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The triple modular redundancy transformation   
#</h1>#    
-   Expressing and proving the main correctness theorem (TTR_correct)

              Pascal Fradet - Inria - 2014  
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)
Add LoadPath "..\Common\".

Require Export ttrStepg.

Set Implicit Arguments.


(* ####################################################### *)
(** **    Triplicated signals and streams                  *)
(**           Used to express properties                   *)
(* ####################################################### *)


(**                Triplicating streams                    *)

CoFixpoint triplStream S (Pis: Stream {|S|}) : Stream {|S|}:=
match Pis with  
Cons Pi Pis => Cons Pi (Cons Pi (Cons Pi (triplStream Pis)))
end.

(** In a stream of triplicated values            *)
(** only 1 out of 3 might be corrupted           *)
CoInductive c1in3_Pos : forall A, Stream {|A|} -> Stream {|A#(§#§)|} -> Prop :=
| C1in3P1 : forall A (a:{|A|}) x s s3, 
            c1in3_Pos s s3 -> c1in3_Pos (Cons a s) (Cons x           (Cons {a,{~0,~0}} (Cons {a,{~0,~0}}  s3)))
| C1in3P2 : forall A (a:{|A|}) x s s3, 
            c1in3_Pos s s3 -> c1in3_Pos (Cons a s) (Cons {a,{~1,~1}} (Cons x           (Cons {a,{~0,~0}}  s3)))
| C1in3P3 : forall A (a:{|A|}) x s s3, 
            c1in3_Pos s s3 -> c1in3_Pos (Cons a s) (Cons {a,{~1,~1}} (Cons {a,{~0,~0}} (Cons x s3))).
Hint Constructors c1in3_Pos.

(** Tags for the different cycles  *)
Inductive Tstep := Step0 | Step1 | Step2.

Definition  ttrsn S T (n:Tstep) (x c c' : circuit S T) :=
match n with
| Step0 => ttrs0 x c 
| Step1 => ttrs1 c c'
| Step2 => ttrs2 c c'
end.

(** Relating a stream and its triplcated version at different cycles *)
CoFixpoint triplStreamOut0 S (Pis: Stream {|S|}) : Stream {|S#(§#§)|}:=
match Pis with  
Cons Pi Pis => Cons {Pi,{~1,~1}} (Cons {Pi,{~0,~0}} (Cons {Pi,{~0,~0}} (triplStreamOut0 Pis)))
end.

CoFixpoint triplStreamOut1 S (Pis: Stream {|S|}) : Stream {|S#(§#§)|}:=
match Pis with  
Cons Pi1 (Cons Pi2 Pis) => Cons {Pi1,{~0,~0}} (Cons {Pi1,{~0,~0}} (Cons {Pi2,{~1,~1}} 
                           (triplStreamOut1 (Cons Pi2 Pis))))
end.

CoFixpoint triplStreamOut2 S (Pis: Stream {|S|}) : Stream {|S#(§#§)|}:=
match Pis with  
Cons Pi1 (Cons Pi2 Pis) => Cons {Pi1,{~0,~0}} (Cons {Pi2,{~1,~1}} (Cons {Pi2,{~0,~0}} 
                           (triplStreamOut2 (Cons Pi2 Pis))))
end.

Definition triplStreamOutn S (n:Tstep) (Pis: Stream {|S|}) : Stream {|S#(§#§)|}:=
match n with
| Step0 => triplStreamOut0 Pis
| Step1 => triplStreamOut1 Pis
| Step2 => triplStreamOut2 Pis
end.

(* c2v holds if the next two values of the stream are correct.          *)
(* It implies that there cannot be an erreur in a window of three steps *)

CoInductive c2v : forall A, Tstep -> nat -> Stream {|A|} -> Stream {|A#(§#§)|} -> Prop :=
| C2v01 : forall A (a:{|A|}) n s s3, 
          c2v Step1 (pred n) (Cons a s) s3 
       -> c2v Step0 n (Cons a s) (Cons {a,{~1,~1}} s3)
| C2v02 : forall A (a:{|A|}) x s s3, 
          c2v Step1 3 (Cons a s) s3 
       -> c2v Step0 0 (Cons a s) (Cons x s3)
| C2v11 : forall A (a:{|A|}) n s s3, 
         c2v Step2 (pred n) (Cons a s) s3 
      -> c2v Step1 n (Cons a s) (Cons {a,{~0,~0}} s3) 
| C2v12 : forall A (a:{|A|}) x s s3, 
         c2v Step2 3 (Cons a s) s3 
      -> c2v Step1 0 (Cons a s) (Cons x  s3) 
| C2v21 : forall A (a b:{|A|}) n s s3, 
         c2v Step0 (pred n) (Cons b s) s3 
      -> c2v Step2 n (Cons a (Cons b s)) (Cons {a,{~0,~0}} s3)
| C2v22 : forall A (a b:{|A|}) x s s3, 
         c2v Step0 3 (Cons b s) s3 
      -> c2v Step2 0 (Cons a (Cons b s)) (Cons x  s3).
Hint Constructors c2v. 

(** c2v implies that in a stream of triplicated values  *)
(** only 1 out of 3 might be corrupted                  *)

Lemma c2v_imp_c1in3 : forall S n (Pi: Stream {|S|}) (Po:Stream {|S#(§#§)|}), 
                      c2v Step0 n Pi Po -> c1in3_Pos Pi Po.
Proof.
cofix CIH. introv H.
Inverts H.
- Inverts H4.
  + Inverts H5; constructor; eapply CIH; exact H4.
  + Inverts H5. constructor. eapply CIH; exact H6.
- Inverts H4. Inverts H5. constructor. 
  Apply CIH with H4.
Qed.

(* The considered fault model where at most 1 out of 4 cycles might incur a glitch *)

Definition set14_eval := set1K_eval 4.

(** Lemmas about triplicated Streams (starting at different cycles) *)

Lemma eq_tS01 : forall S (a:{|S|}) s,
                EqSt (triplStreamOut0 (Cons a s)) (Cons {a,{~1,~1}} (triplStreamOut1 (Cons a s))).
Proof.
cofix CIH. 
introv. destruct s as [b s]. 
rewrite (unfold_Stream (triplStreamOut0 _)). 
rewrite (unfold_Stream (triplStreamOut1 _)). 
do 3 (constructor; try easy).
Qed.


Lemma eq_tS21 : forall S (a b:{|S|}) s,
                EqSt (Cons {a,{~0,~0}} (Cons {b,{~1,~1}} (triplStreamOut1 (Cons b s))))
                     (triplStreamOut2 (Cons a (Cons b s))) .
Proof.
cofix CIH. 
introv. destruct s as [c s]. 
rewrite (unfold_Stream (triplStreamOut2 _)). 
rewrite (unfold_Stream (triplStreamOut1 _)). 
do 3 (constructor; try easy).
Qed.


Lemma eq_tS20 : forall S (a:{|S|}) s,
                EqSt (Cons {a,{~1,~1}} (Cons {a,{~0,~0}} (triplStreamOut2 (Cons a s))))
                     (triplStreamOut0 (Cons a s)) .
Proof.
cofix CIH. 
introv. destruct s as [c s]. 
rewrite (unfold_Stream (triplStreamOut2 _)). 
rewrite (unfold_Stream (triplStreamOut0 _)). 
do 3 (constructor; try easy).
Qed.

Lemma eq_tS10 : forall S (a b:{|S|}) s,
                EqSt (Cons {a, {~0, ~0}} (Cons {a, {~0,~0}} (triplStreamOut0 (Cons b s))))
                     (triplStreamOut1 (Cons a (Cons b s))).
Proof.
cofix CIH. 
introv. destruct s as [c s]. 
rewrite (unfold_Stream (triplStreamOut1 _)). 
rewrite (unfold_Stream (triplStreamOut0 _)). 
do 3 (constructor; try easy).
Qed.

Lemma eqst_imp_set14 : forall S T (c:circuit S T) n Pis1 Pis2 Pos,
                        EqSt Pis1 Pis2 -> set14_eval c n Pis1 Pos -> set14_eval c n Pis2 Pos.
Proof.
cofix CIH.
introv E H. destruct Pis1. destruct Pis2. 
Inverts E. simpl in *. subst.
Inverts H.
- econstructor.
  + exact H8.
  + eapply CIH. exact H1. easy.
- eapply set1K_eval2.
  + exact H8.
  + eapply CIH. exact H1. easy.
Qed.

(** Correctness of the transformation when no glitch occur *)

Theorem set14_eval_correct : forall S T (s012:Tstep) (x c c' :circuit S T) (c3: circuit (S#(§#§)) (T#(§#§))) 
                                        n Pi Pis Po Pos Pos3, 
                             pureStream (Cons Pi Pis) 
                          -> step c Pi Po c' 
                          -> eval c' Pis Pos 
                          -> ttrsn s012 x c c' c3
                          -> set14_eval c3 n (triplStreamOutn s012 (Cons Pi Pis)) Pos3
                          -> c2v s012 n (Cons Po Pos) Pos3.
Proof.
cofix CIH. introv P H G R E. dupl P X. Inverts X. destruct s012.
(* step 0 *)
- rewrite (unfold_Stream (triplStreamOutn _ _)) in E. simpl in E.
  Inverts G. Inverts E. 
  + Apply step_ttrs0 with H in R.
    destruct R as [c31 [H15 R]]. Detstep H11 H15.
    constructor.
    apply eqst_imp_set14 with (Pis2:=triplStreamOut1 (Cons Pi (Cons Pi0 Pis0))) in H12;
    try apply eq_tS10.
    eapply CIH with (x:=c). exact P. exact H. econstructor. exact H7. exact H8.
                            exact R. exact H12.
  + Apply stepgl_ttrs0 with H H11 in R.
    Inverts H12. Inverts H14. 
    rewrite (unfold_Stream (triplStreamOut0 _)) in H15.
    Inverts H15. Inverts H4.
    destruct R as [R | [? R]].
    * Apply step_ttrg1_d1kA with H H7 H12 H13 in R.
      destruct R as [? R]. destruct Pis0. subst. 
      Apply step_ttrg2_d2 with H H12 in R.
      destruct R as [? R]. subst.
      Apply step_ttrg0_d3 with H7 H14 in R.
      destruct R as [? R]. subst.
      apply eqst_imp_set14 with (Pis2:=triplStreamOut1 (Cons Pi0 (Cons b Pis0))) in H16;
      try apply eq_tS01.
      do 4 constructor.
      eapply CIH with (x:=c'). 2: exact H7.  2: exact H8. 2: exact R. 2: exact H16. constructor; easy.
    * Apply step_ttrg1_d2d3kB with H H12 H13 in R.
      destruct R as [? [? R]]. subst. 
      Apply ttrs0_step with H7 H14 in R.
      destruct R as [? R]. subst.
      apply eqst_imp_set14 with (Pis2:=triplStreamOut1 (Cons Pi0 Pis0)) in H16;
      try apply eq_tS01. 
      do 4 constructor.    
      eapply CIH with (x:=c). 2: exact H7. 2: exact H8. 2: exact R. 2: exact H16. constructor; easy. 
(* step 1 *)
- rewrite (unfold_Stream (triplStreamOutn _ _)) in E. simpl in E.
  Inverts G. Inverts E. 
  + Apply step_ttrs1 with H in R.
    destruct R as [c31 [H15 R]]. Detstep H11 H15.
    constructor.
    apply eqst_imp_set14 with (Pis2:=triplStreamOut2 (Cons Pi (Cons Pi0 Pis0))) in H12;
          try apply eq_tS21. 
    eapply CIH  with (x:=c). exact P. exact H. econstructor. 
                             exact H7. exact H8. exact R. exact H12. 
  + Apply stepgl_ttrs1 with H H11 in R.
    Inverts H12. Inverts H14. 
    destruct Pis0. rewrite (unfold_Stream (triplStreamOut1 _)) in H15.
    Inverts H15. Inverts H4.
    destruct R as [R |[? R]].
    * Apply step_ttrg2_d1kA with H H7 H13 in R. 
      destruct R as [? R]. subst.
      destruct Pis0. 
      Apply step_ttrg0_d2 with H7 H12 in R.
      destruct R as [? R]. subst.
      Apply step_ttrg1_d3 with H7 H14 in R.
      destruct R as [? R]. subst.
      apply eqst_imp_set14 with (Pis2:=triplStreamOut2 (Cons Pi0 (Cons b (Cons b0 Pis0)))) in H16;
      try apply eq_tS21.
      do 4 constructor.
      eapply CIH with (x:=c'). 2: exact H7. 2: exact H8. 2: exact R. 
                               2: exact H16. constructor; easy.
    * Apply step_ttrg2_d2d3kB with H H7 H13 H12 in R.
      destruct R as [? [? R]]. subst. 
      Apply ttrs1_step with H7 H14 in R.
      destruct R as [? R]. subst.
      apply eqst_imp_set14 with (Pis2:=triplStreamOut2 (Cons Pi0 (Cons b Pis0))) in H16;
      try apply eq_tS21. 
      do 4 constructor.    
      eapply CIH with (x:=c'). 2: exact H7. 2: exact H8. 2: exact R. 
                               2: exact H16. constructor; easy. 
(* step 2 *)
- rewrite (unfold_Stream (triplStreamOutn _ _)) in E. simpl in E.
  Inverts G. Inverts E. 
  + Apply step_ttrs2 with H in R.
    destruct R as [c31 [H15 R]]. Detstep H11 H15.
    constructor.
    apply eqst_imp_set14 with (Pis2:=triplStreamOut0 (Cons Pi0 Pis0)) in H12;
          try apply eq_tS20. 
    eapply CIH with (x:=c). exact H4. exact H7. exact H8. exact R. exact H12.
  + Apply stepgl_ttrs2 with H H11 in R.
    Inverts H12. Inverts H14. 
    destruct Pis0. rewrite (unfold_Stream (triplStreamOut2 _)) in H15.
    Inverts H15. Inverts H4.
    destruct R as [R |[? R]].
    * Apply step_ttrg0_d1kA with H H7 H12 H13 in R.
      destruct R as [? R]. subst.
      destruct Pis0. 
      Apply step_ttrg1_d2 with H7 H12 in R.
      destruct R as [? R]. subst.
      Apply step_ttrg2_d3 with H7 H12 H14 in R.
      destruct R as [? R]. subst.
      apply eqst_imp_set14 with (Pis2:=triplStreamOut0 (Cons b (Cons b0 Pis0))) in H16;
      try apply eq_tS20. destruct Pos1. destruct Pos0.
      do 4 constructor. Inverts H8.
      eapply CIH with (x:=c'). exact H6. exact H15. exact H18. exact R. exact H16.
    * Apply step_ttrg0_d2d3kB with H H7 H12 H13 in R.
      destruct R as [? [? R]]. subst. 
      Apply ttrs2_step with H7 H14 in R.
      destruct R as [? R]. subst.
      apply eqst_imp_set14 with (Pis2:=triplStreamOut0 (Cons b Pis0)) in H16;
      try apply eq_tS20. destruct Pos1. destruct Pos0.
      do 4 constructor. Inverts H8.    
      eapply CIH with (x:=c'). exact H6. exact H15. exact H18. exact R. exact H16.
Qed.


Lemma ttr_correct : forall S T (c:circuit S T) n Pis Pos Pos3, 
                      pureStream Pis
                   -> eval c Pis Pos 
                   -> set14_eval (ttr c) n (triplStreamOut0 Pis) Pos3
                   -> c1in3_Pos Pos Pos3.
Proof.
introv P E H.
assert (R:ttrs0 c c (ttr c)) by (apply ttr_equiv_ttrs0; easy).
Inverts E.
replace (triplStreamOut0 (Cons Pi Pis0))
   with (triplStreamOutn Step0 (Cons Pi Pis0)) in H by easy. 
Apply set14_eval_correct with P R H5 H6 in H.
Apply c2v_imp_c1in3 with H. 
Qed.

(** In SET(1,K) models, an execution allowed to inject a glitch right away (set1K_eval K c 0) *)
(** can do the same steps as the execution allowed to inject a glitch                         *)
(** after more steps (set1K_eval K c 0) i.e., there is never an obligation to insert a glitch *)

Lemma set1K_n_imp_set1K_0  : forall S T (c:circuit S T) K n Pis Pos, 
                             set1K_eval K c n Pis Pos 
                          -> set1K_eval K c 0 Pis Pos.
Proof.
cofix CIH.
introv H.
destruct Pis. Inverts H.
- Apply set1K_eval1 with H7. 
  Apply CIH with H8. 
- Apply set1K_eval2 with H7. 
Qed.

(** Lemmas used to minimize the cost of the guarded condition check in supp_cb_ttr *)
(** Without that exponentially costly check, they would be within supp_cb_ttr.     *)

Lemma fact0_stepg_cb2 : forall S T s s1 t1 (c c0:circuit (S # (§ # §)) (T # (§ # §)))  cb0 a Pis Pos,
                        stepg (cb_ttr2 S) s s1 cb0 
                     -> step c s1 t1 c0
                     -> set14_eval (cb0 -o- c0) 3 (Cons a (Cons a (Cons a Pis))) Pos
                     -> (s1={s,{~0,~0}} \/ s1={s,{~0,~?}} \/ s1={s,{~?,~0}})
                        /\ exists b1 b2 b3 c1 c2 c3 Pos',
                              Pos=Cons b1 (Cons b2 (Cons b3 Pos'))
                           /\ set14_eval ((cb_ttr S)-o-c3) 0 Pis Pos'
                           /\ step c0 {a,{~1,~1}} b1 c1
                           /\ step c1 {a, {~ 0, ~ 0}} b2 c2
                           /\ step c2 {a, {~ 0, ~ 0}} b3 c3. 
Proof.
introv H G1 G2.
apply fact_stepg_cb2 in H.
destruct H as [[H|[H|H]] [b1[b2[b3[b4[b5[b6[? H1]]]]]]]]; subst.
- Inverts G2. Invstep H7.
  Apply fact_step_ccb0 with H2 in H4. SimpS.
  Inverts H8. Invstep H9.
  eapply fact_step_cb1i in H5. SimpS. 
  Inverts H10. Invstep H9.
  eapply fact_step_cb2i in H6. SimpS.
  split. easy.
  exists {x7, {x8, x9}} {x14, {x15, x16}} {x, {x18, x19}}.
  exists x6 x12 x17 Pos0. easy.
- Inverts G2. Invstep H7.
  Apply fact_step_ccb0 with H2 in H4. SimpS.
  Inverts H8. Invstep H9.
  eapply fact_step_cb1i in H5. SimpS. 
  Inverts H10. Invstep H9.
  eapply fact_step_cb2i in H6. SimpS.
  split. easy.
  exists {x7, {x8, x9}} {x14, {x15, x16}} {x, {x18, x19}}.
  exists x6 x12 x17 Pos0. easy.
- Inverts G2. Invstep H7.
  Apply fact_step_ccb0 with H2 in H4. SimpS.
  Inverts H8. Invstep H9.
  Apply fact_step_cb1i in H5. SimpS. 
  Inverts H10. Invstep H9.
  Apply fact_step_cb2i in H6. SimpS.
  split. easy.
  exists {x7, {x8, x9}} {x14, {x15, x16}}  {x, {x18, x19}}.
  exists x6 x12 x17 Pos0. easy. 
Qed.


Lemma fact0_stepg_cb1 : forall S T s s1 t1 (c c0:circuit (S # (§ # §)) (T # (§ # §)))  cb0 a Pis Pos,
                        stepg (cb_ttr1 S) s s1 cb0 
                     -> step c s1 t1 c0
                     -> set14_eval (cb0 -o- c0) 3 (Cons a Pis) Pos
                     -> (s1={s,{~0,~0}} \/ s1={s,{~0,~?}} \/ s1={s,{~?,~0}})
                        /\ exists b1 c1 Pos',
                              Pos=Cons b1 Pos'
                           /\ set14_eval ((cb_ttr S)-o-c1) 2 Pis Pos'
                           /\ step c0 {a,{~0,~0}} b1 c1. 
Proof.
introv H G1 G2.
apply fact_stepg_cb1 in H.
destruct H as [[H|[H|H]] [b1[b2[b3[b4[b5[b6[? H1]]]]]]]]; subst.
- Inverts G2. Invstep H7.
  Apply fact_step_ccb2 with H2 in H4. SimpS.
  split. easy.
  exists {x, {x7, x8}} x6 Pos0.
  split; easy.
- Inverts G2. Invstep H7.
  Apply fact_step_ccb2 with H2 in H4. SimpS.
  split. easy.
  exists {x, {x7, x8}} x6 Pos0.
  split; easy.
- Inverts G2. Invstep H7.
  Apply fact_step_ccb2 with H2 in H4. SimpS.
  split. easy.
  exists {x, {x7, x8}} x6 Pos0.
  split; easy.
Qed.

Lemma fact0_stepg_cb0 : forall S T s s1 t1 (c c0:circuit (S # (§ # §)) (T # (§ # §)))  cb0 a Pis Pos,
                        stepg (cb_ttr S) s s1 cb0 
                     -> step c s1 t1 c0
                     -> set14_eval (cb0 -o- c0) 3 (Cons a (Cons a Pis)) Pos
                     -> (s1={s,{~1,~1}} \/ s1={s,{~1,~?}} \/ s1={s,{~?,~1}})
                        /\ exists b1 b2 c1 c2 Pos',
                              Pos=Cons b1 (Cons b2 Pos')
                           /\ set14_eval ((cb_ttr S)-o-c2) 1 Pis Pos'
                           /\ step c0 {a,{~0,~0}} b1 c1
                           /\ step c1 {a,{~0,~0}} b2 c2. 
Proof.
introv H G1 G2.
apply fact_stepg_cb0 in H.
destruct H as [[H|[H|H]] [b1[b2[b3[b4[b5[b6[? H1]]]]]]]]; subst.
- Inverts G2. Invstep H7.
  Apply fact_step_ccb1 with H2 in H4. SimpS.
  split. easy.
  Inverts H8. Invstep H9.
  eapply fact_step_cb2i in H5. SimpS.
  exists {x7, {x8, x9}} {x, {x14, x15}} x6 x12 Pos. easy.
- Inverts G2. Invstep H7.
  Apply fact_step_ccb1 with H2 in H4. SimpS.
  split. easy.
  Inverts H8. Invstep H9.
  eapply fact_step_cb2i in H5. SimpS.
  exists {x7, {x8, x9}} {x, {x14, x15}} x6 x12 Pos.
  easy.
- Inverts G2. Invstep H7.
  Apply fact_step_ccb1 with H2 in H4. SimpS.
  Inverts H8. Invstep H9.
  eapply fact_step_cb2i in H5. SimpS.
  split. easy.
  exists {x7, {x8, x9}} {x, {x14, x15}} x6 x12 Pos.
  easy.
Qed.

Lemma supp_cb_ttr : forall S T (c:circuit (S # (§ # §)) (T # (§ # §))) n Pis Pos3, 
                    pureStream Pis
                 -> set14_eval ((cb_ttr S) -o- c) n (triplStream Pis) Pos3 
                 -> set14_eval c n (triplStreamOut0 Pis) Pos3.
Proof.
cofix CIH. introv P H.
destruct Pis as [Pi Pis]. Inverts P.
rewrite (unfold_Stream (triplStream _)) in H. simpl in H.
rewrite (unfold_Stream (triplStreamOut0 _)). simpl.
Inverts H.
- Inverts H9.
  apply fact_step_ncb0 in H5. SimpS.
  econstructor. exact H12. 
  Inverts H10.
  + Inverts H8. apply fact_step_ncb1 in H5. SimpS.
    econstructor. exact H13. 
    Inverts H9.
    * Inverts H8. apply fact_step_ncb2 in H5. SimpS. 
      econstructor. exact H14.
      Apply CIH. 
    * Inverts H8.
    { Inverts H11.  
      apply fact_step_ncb2 in H6. SimpS. 
      eapply set1K_eval2.
      Apply Satinput with H16.
      Apply CIH. }
    { Inverts H9.
      - destruct Pis as [Pi1 Pis]. 
        rewrite (unfold_Stream (triplStream _)) in H10. simpl in H10.
        rewrite (unfold_Stream (triplStreamOut0 _)). simpl. 
        eapply fact0_stepg_cb2 in H6; try exact H15; try exact H10.
        destruct H6 as [G0[b1[b2[b3[c1[c2[c3[Pos'[G1[G2[G3[G4 G5]]]]]]]]]]]].  
        Inverts H4. destruct G0 as [G0|[G0|G0]]; 
        [subst; eapply set1K_eval1; try exact H15
        | subst; eapply set1K_eval2; 
          try eapply Satinput; try exact H15;
          try apply Tpinr; try constructor; try constructor
        | subst; eapply set1K_eval2; 
          try eapply Satinput; try exact H15;
          try apply Tpinr; try constructor; try constructor];
          eapply set1K_eval1; try exact G3;
          eapply set1K_eval1; try exact G4;
          eapply set1K_eval1; try exact G5;
          eapply CIH; easy. 
      - apply fact_step_ncb2 in H6. SimpS.
        eapply set1K_eval2. Apply Safterlg with H15.
        Apply CIH. }
  + Inverts H8.
    * Inverts H11. 
      apply fact_step_ncb1 in H6. SimpS. 
      eapply set1K_eval2. Apply Satinput with H15.
      Inverts H9. Inverts H11. 
      apply fact_step_ncb2 in H6. SimpS. 
      econstructor. exact H16.
      Apply CIH.
    * Inverts H10.
      { Apply fact0_stepg_cb1 with H14 H9 in H6.
        destruct H6 as [[H6|[H6|H6]] [b1[b2[b3[G1[G2 G3]]]]]]; subst.
        + Apply set1K_eval1 with H14.
          Apply set1K_eval1 with G3.
          apply set1K_n_imp_set1K_0 in G2. 
          Apply CIH. 
        + eapply set1K_eval2. 
          Apply Satinput with H14.
          Apply set1K_eval1 with G3.
          Apply CIH. 
        + eapply set1K_eval2. 
          Apply Satinput with H14.
          Apply set1K_eval1 with G3.
          Apply CIH. }
     { apply fact_step_ncb1 in H6. SimpS.
       eapply set1K_eval2. Apply Safterlg with H14.
       Inverts H9. Inverts H10. 
       apply fact_step_ncb2 in H6. SimpS. 
       econstructor. exact H15.
       Apply CIH. }
-  Inverts H9. 
  + Inverts H8. 
    apply fact_step_ncb0 in H5. SimpS.
    eapply set1K_eval2.
    Apply Satinput with H13.
    Inverts H10. Inverts H9.
    apply fact_step_ncb1 in H5. SimpS.
    econstructor. exact H14.
    Inverts H11. Inverts H9. 
    apply fact_step_ncb2 in H5. SimpS.
    econstructor. exact H15.
    Apply CIH.
  + Inverts H7.
    * Apply fact0_stepg_cb0 with H10 H12 in H5.
      destruct H5 as [[H5|[H5|H5]]  [b1[b2[c1[c2[Po1[G1[G2 [G3 G4]]]]]]]]]; subst.
      { Apply set1K_eval1 with H12.
        Apply set1K_eval1 with G3.
        Apply set1K_eval1 with G4.
        apply set1K_n_imp_set1K_0 in G2.
        Apply CIH. }
      { eapply set1K_eval2. 
        Apply Satinput with H12.
        Apply set1K_eval1 with G3.
        Apply set1K_eval1 with G4.
        Apply CIH. }
      { eapply set1K_eval2. 
        Apply Satinput with H12.
        Apply set1K_eval1 with G3.
        Apply set1K_eval1 with G4.
        Apply CIH. }
    * apply fact_step_ncb0 in H5. SimpS.
      eapply set1K_eval2. Apply Safterlg with H12.
      Inverts H10. Inverts H8. 
      apply fact_step_ncb1 in H5. SimpS.
      econstructor. exact H13.
      Inverts H9. Inverts H8.
      apply fact_step_ncb2 in H5. SimpS.
      econstructor. exact H14.
      Apply CIH.
Qed.

Theorem TTR_correct : forall S T (c:circuit S T) n Pis Pos Pos3, 
                      pureStream Pis
                   -> eval c Pis Pos 
                   -> set14_eval (TTR c) n (triplStream Pis) Pos3
                   -> c1in3_Pos Pos Pos3.
Proof.
introv P E H.
Apply supp_cb_ttr in H.
Apply ttr_correct with E in H.
Qed.

(* Print Assumptions TTR_correct. *) 
