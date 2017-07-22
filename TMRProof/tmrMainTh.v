(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The triple modular redundancy transformation   
#</h1>#    
-  A few tactics for TMR
-  Main correctness property for TMR 

            Pascal Fradet - Inria - 2014   
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\Common\".
Require Export tmrPlugs.

Set Implicit Arguments.

Hint Resolve fact_shuf1 fact_shuf2 fact_shuf3 fact_votmr fact1_votmr.

(* A few tactics dedicated to TMR *)
Ltac Stmr := 
repeat match goal with 
    | [H: context[tmr (Cgate _)] |- _]    => unfold tmr in H
    | [H: context[tmr (Cplug _)] |- _]    => unfold tmr in H
    | [H: context[tmr (Cseq _ _)] |- _]   => unfold tmr in H; simpl in H; fold tmr in H
    | [H: context[tmr (Cpar _ _)] |- _]   => unfold tmr in H; simpl in H; fold tmr in H
    | [H: context[tmr (Cloop _ _)] |- _]  => unfold tmr in H; simpl in H; fold tmr in H
    | [ H:step (shuf1 _ _) _ _ ?C |- _] 
       => match C with
        | shuf1 _ _ => fail 1 
        | _       => Combcode H
          end
    | [ H:step (shuf2 _ _) _ _ ?C |- _] 
       => match C with
        | shuf2 _ _ => fail 1 
        | _       => Combcode H
          end
    | [ H:step (shuf3 _) _ _ ?C |- _] 
       => match C with
        | shuf3 _ => fail 1 
        | _       => Combcode H
          end
    | [ H:step (votmr _) _ _ ?C |- _] 
       => match C with
        | votmr _  => fail 1 
        | _       => Combcode H
          end
    | [ H:step (shuf1 _ _) ?x _ _ , H1: corrupt_1in3_bus1 _ ?x|- _] 
       => eapply shuf1_corrupt1 in H; try exact H1; destruct H
    | [ H:step (shuf1 _ _) ?x _ _ , H1: corrupt_1in3_bus2 _ ?x|- _] 
       => eapply shuf1_corrupt2 in H; try exact H1; destruct H
    | [ H:step (shuf1 _ _) ?x _ _ , H1: corrupt_1in3_bus3 _ ?x|- _] 
       => eapply shuf1_corrupt3 in H; try exact H1; destruct H
    | [ H:step (shuf3 _) ?x _ _ , H1: corrupt_1in3_bus1 _ ?x|- _] 
       => eapply shuf3_corrupt1 in H; try exact H1; destruct H
    | [ H:step (shuf3 _) ?x _ _ , H1: corrupt_1in3_bus2 _ ?x|- _] 
       => eapply shuf3_corrupt2 in H; try exact H1; destruct H
    | [ H:step (shuf3 _) ?x _ _ , H1: corrupt_1in3_bus3 _ ?x|- _] 
       => eapply shuf3_corrupt3 in H; try exact H1; destruct H
    | [ H: step (shuf2 _ _) {?x,?y} _ _ , 
        H1: corrupt_1in3_bus1 _ ?x , 
        H2: corrupt_1in3_bus1 _ ?y |- _] 
         => eapply shuf2_corrupt1 in H; try exact H1;  try exact H2
    | [ H: step (shuf2 _ _) {?x,?y} _ _ , 
        H1: corrupt_1in3_bus2 _ ?x , 
        H2: corrupt_1in3_bus2 _ ?y |- _] 
         => eapply shuf2_corrupt2 in H; try exact H1;  try exact H2
    | [ H: step (shuf2 _ _) {?x,?y} _ _ , 
        H1: corrupt_1in3_bus3 _ ?x , 
        H2: corrupt_1in3_bus3 _ ?y |- _] 
         => eapply shuf2_corrupt3 in H; try exact H1;  try exact H2

    | [H: corrupt_1in3_bus1 _ _ |- _] => let X := fresh "X" in dupl H X; revert H; Inverts X 
    | [H: corrupt_1in3_bus2 _ _ |- _] => let X := fresh "X" in dupl H X; revert H; Inverts X 
    | [H: corrupt_1in3_bus3 _ _ |- _] => let X := fresh "X" in dupl H X; revert H; Inverts X 
    | [H: corrupt_1in3_bus _ _ |- _] => let X := fresh "X" in dupl H X; revert H; Inverts X 
end; intros.

Ltac SStmr := Stmr; Simpl.
Ltac Red :=  Stmr; Simpl; Invstep_H; try eauto.
Ltac Crush :=  Simpl; Stmr; Invstep_H; SimpS; Stmr; try eauto. 


(** *            Property of tmr without errors         *)

Lemma tmr_normal : forall S T (c c':circuit S T) s t, 
                   step c s t c' -> step (tmr c) {s,s,s} {t,t,t} (tmr c').
Proof. introv H. induction H; RedstepG. Qed.


(** *               Isolation properties                   *)
(** a fault in 1 of the triplicated inputs stay confined   *) 
(** within the same triplicated part                       *)

Lemma tmr_fault1 : forall S T (c c':circuit S T) ccc s t sss ttt, 
                   pure_bset s
                -> corrupt_1in3_bus1 s sss 
                -> step c s t c' 
                -> step (tmr c) sss ttt ccc
                -> corrupt_1in3_bus1 t ttt /\ corrupt_1in3_cir1 c' ccc.
Proof.
introv I C H1 H2. induction H1; Red.
- Apply IHstep1 in H. SimpS. 
  Apply IHstep2 in H0. SimpS. easy. 
- Apply IHstep1 in H2; Red.
  Apply IHstep2 in H4. Crush.   
- assert (X:step (votmr S) {t0,s,s, bool2bset b, bool2bset b, bool2bset b}
                           {t0, bool2bset b, {s, bool2bset b}, {s, bool2bset b}} (votmr S))
      by (apply fact_votmr).
  SStmr. eapply IHstep in H8; [idtac|Checkpure|easy]. Crush. 
Qed.

Lemma tmr_fault2 : forall S T (c c':circuit S T) ccc s t sss ttt, 
                   pure_bset s
                -> corrupt_1in3_bus2 s sss 
                -> step c s t c' 
                -> step (tmr c) sss ttt ccc
                -> corrupt_1in3_bus2 t ttt /\ corrupt_1in3_cir2 c' ccc.
Proof.
introv I C H1 H2. induction H1; Red.
- Apply IHstep1 in H. SimpS. 
  Apply IHstep2 in H0. SimpS. easy. 
- Red. Apply IHstep1 in H2.
  Apply IHstep2 in H4. Crush.  
- assert (X:step (votmr S) {s,t0,s, bool2bset b, bool2bset b, bool2bset b}
                           {s, bool2bset b, {t0, bool2bset b}, {s, bool2bset b}} (votmr S))
      by (apply fact_votmr).
  SStmr. eapply IHstep in H8; [idtac|Checkpure|easy]. Crush. 
Qed.


Lemma tmr_fault3 : forall S T (c c':circuit S T) ccc s t sss ttt, 
                   pure_bset s
                -> corrupt_1in3_bus3 s sss 
                -> step c s t c' 
                -> step (tmr c) sss ttt ccc
                -> corrupt_1in3_bus3 t ttt /\ corrupt_1in3_cir3 c' ccc.
Proof.
introv I C H1 H2. induction H1; Red.
- Apply IHstep1 in H. SimpS. 
  Apply IHstep2 in H0. SimpS. easy. 
- Red. Apply IHstep1 in H2.
  Apply IHstep2 in H4. Crush.  
- assert (X:step (votmr S) {s,s,t0, bool2bset b, bool2bset b, bool2bset b}
                           {s, bool2bset b, {s, bool2bset b}, {t0, bool2bset b}} (votmr S)) 
      by (apply fact_votmr).
  SStmr. eapply IHstep in H8; [idtac|Checkpure|easy]. Crush. 
Qed.

(** The corrupted part of a TMRed circuit "repairs" itself after  *)
(** one normal reduction step.                                    *)
  
Lemma tmr_corruptc : forall S T (c c':circuit S T) ccc s t, 
                     pure_bset s
                  -> corrupt_1in3_cir c ccc 
                  -> step c s t c' 
                  -> step ccc {s,s,s} {t,t,t} (tmr c').
Proof.
introv I C H. induction c. 
- Inverts C; Inverts H4; Red; easy.
- Inverts C; Inverts H4; Red; easy. 
- apply ccir_seq in C. Red. Purestep H.
  Apply IHc1 with H0 in H.
  Apply IHc2 with H1 in H2.  
  RedstepG.
- apply ccir_par in C. Red. 
  Apply IHc1 with H4 in H.
  Apply IHc2 with H5 in H6.  
  RedstepG.
- apply ccir_loop in C. SimpS.
  Red; solve [Apply IHc with H1 in H; RedstepG].
Qed.

(** A glitch in a reduction step may corrupt only one copy of  *)
(** the circuit and the outputs.                               *)

Lemma tmr_stepg  : forall S T (c c':circuit S T) ccc s t ttt, 
                   pure_bset s 
                -> step c s t c' 
                -> stepg (tmr c) {s,s,s} ttt ccc
                -> (corrupt_1in3_bus1 t ttt /\ corrupt_1in3_cir1 c' ccc)
                \/ (corrupt_1in3_bus2 t ttt /\ corrupt_1in3_cir2 c' ccc)
                \/ (corrupt_1in3_bus3 t ttt /\ corrupt_1in3_cir3 c' ccc).
Proof.
introv I H G. Dd_buset ttt. induction H.
- simpl in G. Crush.
- simpl in G. Crush. 
- Inverts G; Dd_buset t0.
  + Apply IHstep1 in H5; try easy.
    Red. destruct H5 as [[H5 H6]|[[H5 H6]|[H5 H6]]].
    * eapply tmr_fault1 with (c:=c2) (c':=c2') (ccc:=c2'0) (t:=u) (ttt:={x4, x5, x3}) 
                        in H5; try easy.
      Red. 
    * apply tmr_fault2 with (c:=c2) (c':=c2') (ccc:=c2'0) (t:=u) (ttt:={x4, x5, x3})
                       in H5; try easy.
      Red.
    * apply tmr_fault3 with (c:=c2) (c':=c2') (ccc:=c2'0) (t:=u) (ttt:={x4, x5, x3}) 
                       in H5; try easy.
      Red. 
  + apply tmr_normal in H. Red. 
    eapply IHstep2 with (ccc:=c2'0) in H10; try easy.
    destruct H10 as [[? ?]|[[? ?]|[? ?]]]; 
    eauto using cle11_tmr, cle12_tmr, cle13_tmr.
- set (X:= @fact_shuf1 S U s s s u u u). 
  simpl in G. Invstep G; Red.
  + Apply IHstep1 in H0. 
    eapply tmr_normal in H3. 
    destruct H0 as [[? ?] | [[? ?] | [? ?]] ]; Red;
    [ eapply shuf2_corrupt1 with (a:=x4) (b:=v) in H1; try easy
    | eapply shuf2_corrupt2 with (a:=x4) (b:=v) in H1; try easy
    | eapply shuf2_corrupt3 with (a:=x5) (b:=v) in H1; try easy];
    eauto using cle11_tmr, cle12_tmr, cle13_tmr. 
  + eapply tmr_normal in H2. 
    Apply IHstep2 in H4. 
    destruct H4 as [[? ?] | [[? ?] | [? ?]] ]; Red;
    [ eapply shuf2_corrupt1 with (a:=t) (b:=x2) in H1; try easy 
    | eapply shuf2_corrupt2 with (a:=t) (b:=x2) in H1; try easy
    | eapply shuf2_corrupt3 with (a:=t) (b:=x3) in H1; try easy];
    eauto using cle11_tmr, cle12_tmr, cle13_tmr. 
- simpl in G. Invstep G; Red. 
  + Apply fact2_votmr in H. Inverts H; SimpS.
    * Apply tmr_fault3 with H6 in H4. SimpS. Red.
    * Apply tmr_fault2 with H6 in H4. SimpS. Red.
    * Apply tmr_fault1 with H6 in H4. SimpS. Red. 
  + set (X:= @fact_votmr S s s s (bool2bset b)).
    Red. Apply IHstep in H4.
    destruct H4 as [[? ?] | [[? ?] | [? ?]] ]; Red.
  + assert (X:introglitch {bool2bset b, bool2bset b, bool2bset b} 
                          {bool2bset b, bool2bset b, x19}) by easy.
    apply fact3_introglitch in X.
    apply fact1_votmr with (a:=s) in X.
    Red. Apply tmr_fault3 with H7 in H5. 
    SimpS. Red. 
  + assert (X:introglitch {bool2bset b, bool2bset b, bool2bset b} 
                          {bool2bset b, x17, bool2bset b}) by easy.
    apply fact3_introglitch in X.
    apply fact1_votmr with (a:=s) in X. Red.
    Apply tmr_fault2 with H7 in H5. 
    SimpS. Red.
  + assert (X:introglitch {bool2bset b, bool2bset b, bool2bset b} 
                          {x15, bool2bset b, bool2bset b}) by easy.
    apply fact3_introglitch in X.
    apply fact1_votmr with (a:=s) in X. Red.
    Apply tmr_fault1 with H7 in H5.
    SimpS. Red.
Qed.

(** Direct corrolary : A glitch in a reduction step may       *)
(** corrupt only one copy of the primary outputs.             *)

Corollary tmr_stepg_s : forall S T (c c':circuit S T) ccc s t ttt, 
                   pure_bset s 
                -> step c s t c' 
                -> stepg (tmr c) {s,s,s} ttt ccc
                -> corrupt_1in3_bus t ttt.
Proof.
introv I H G. 
Apply tmr_stepg with H in G.
destruct G as [[X ?]|[[X ?]|[X ?]]]; Inverts X; easy.
Qed.

(** Direct corrolary : A glitch in a reduction step may       *)
(** corrupt only one copy of the triplicated circuit.            *)
 
Corollary tmr_stepg_c : forall S T (c c':circuit S T) ccc s t ttt, 
                   pure_bset s 
                -> step c s t c' 
                -> stepg (tmr c) {s,s,s} ttt ccc
                -> corrupt_1in3_cir c' ccc.
Proof.
introv I H G. 
Apply tmr_stepg with H in G.
destruct G as [[? ?]|[[? ?]|[? ?]]]; easy.
Qed.


(** *       General correctness property for TMR          *)
(** tmr transformation ensures correctness under the      *)
(** fault-model SET (1,2) ie a tmr circuit produces       *)
(** a triplicated output stream with at most 1 corrupted  *)
(** out of 3 copies of the output stream without fault    *)

Definition set12_eval := set1K_eval 2.

Theorem tmr_correct : forall S T (c:circuit S T) n Pis Pos Posss, 
                      pureStream Pis
                   -> eval c Pis Pos 
                   -> set12_eval (tmr c) n (tmrStream Pis) Posss
                   -> corrupt_1in3_stream Pos Posss. 
Proof.
cofix CIH.
introv B E H. Inverts E. Inverts H.
- rewrite (unfold_Stream (tmrStream (Cons Pi Pis0))) in H0.
  simpl in H0. Inverts H0. Inverts B.
  eapply tmr_normal in H5. Red.
  constructor. easy.
  eapply CIH; [exact H3 | exact H6 |exact H9].
- Inverts H6. Inverts B. Inverts H4. 
  rewrite (unfold_Stream (tmrStream (Cons Pi (Cons Pi1 Pis1)))) in H0. simpl in H0. 
  rewrite (unfold_Stream (tmrStream (Cons Pi1 Pis1))) in H0. simpl in H0. 
  Inverts H0. Inverts H8. Inverts H9.
  + apply fact3_introglitch in H13.
   Inverts H13. 
   * Apply tmr_fault3  with H3 H5 in H14. SimpS. 
     Apply tmr_corruptc with H6 in H7; try (apply Ccle1_3; try exact H0).
     repeat (constructor; try easy); Red. 
   * Apply tmr_fault2  with H3 H5 in H14. SimpS. 
     Apply tmr_corruptc with H6 in H7; try (apply Ccle1_2; try exact H0).
     repeat (constructor; try easy); Red. 
   * Apply tmr_fault1  with H3 H5 in H14. SimpS. 
     Apply tmr_corruptc with H6 in H7; try (apply Ccle1_1; try exact H0).
     repeat (constructor; try easy); Red. 
  + Inverts H9. dupl H13 H8.
    Apply tmr_stepg_s with H5 in H13.
    Apply tmr_stepg_c with H5 in H8.
    Apply tmr_corruptc with H7 in H8.
    Rdet. repeat (constructor; try easy). eapply CIH; eauto.
Qed.

(* Print Assumptions tmr_correct. *)
