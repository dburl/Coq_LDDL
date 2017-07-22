
(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The triple modular redundancy transformation   
#</h1>#    
- Lemmas on relations between states 
- Lemmas on reduction with glitch (stepg) 

              Pascal Fradet - Inria - 2014  
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\Common\".

Require Export ttrStep.

Set Implicit Arguments.


(** Lemmas on ttrg0 relations *)
Lemma ttrg0_d2d3kB_lseq : forall S T U (c1 c1':circuit S T) (c2 c2':circuit T U) c31 c32,
                          ttrg0_d2d3kB c1 c1' c31 
                       -> ttrs0 c2 c2' c32 
                       -> ttrg0_d2d3kB (c1-o-c2) (c1'-o-c2') (c31-o-c32).
Proof.
introv H1 H2.
destruct H1 as [H1|[H1|H1]].
- apply ttrs0_imp_ttrg0_d2 in H2.
  left. constructor; easy.
- apply ttrs0_imp_ttrg0_d3 in H2.
  right. left. constructor; easy.
- apply ttrs0_imp_ttrg0_kB in H2.
  right. right. constructor; easy.
Qed.

Lemma ttrg0_d2d3kB_rseq : forall S T U (c1 c1':circuit S T) (c2 c2':circuit T U) c31 c32,
                          ttrs0 c1 c1' c31 
                       -> ttrg0_d2d3kB c2 c2' c32
                       -> ttrg0_d2d3kB (c1-o-c2) (c1'-o-c2') (c31-o-c32).
Proof.
introv H2 H1.
destruct H1 as [H1|[H1|H1]].
- apply ttrs0_imp_ttrg0_d2 in H2.
  left. constructor; easy.
- apply ttrs0_imp_ttrg0_d3 in H2.
  right. left. constructor; easy.
- apply ttrs0_imp_ttrg0_kB in H2.
  right. right. constructor; easy.
Qed.

Lemma ttrg0_d2d3kB_lpar : forall S T U V (c1 c1':circuit S T) (c2 c2':circuit U V) c31 c32,
                          ttrs0 c2 c2' c32 
                       -> ttrg0_d2d3kB c1 c1' c31
                       -> ttrg0_d2d3kB (-|c1,c2|-) (-|c1',c2'|-) 
                          ((SWAP_LR S U (§#§))-o--|c31,ID|--o-(SWAP_LS T (§#§) U)-o--|ID,c32|--o-RSH ).
Proof.
introv H2 H1.
destruct H1 as [H1|[H1|H1]].
- apply ttrs0_imp_ttrg0_d2 in H2.
  left. constructor; easy.
- apply ttrs0_imp_ttrg0_d3 in H2.
  right. left. constructor; easy.
- apply ttrs0_imp_ttrg0_kB in H2.
  right. right. constructor; easy.
Qed.

Lemma ttrg0_d2d3kB_rpar : forall S T U V (c1 c1':circuit S T) (c2 c2':circuit U V) c31 c32,
                          ttrs0 c1 c1' c31 
                       -> ttrg0_d2d3kB c2 c2' c32 
                       -> ttrg0_d2d3kB (-|c1,c2|-) (-|c1',c2'|-) 
                          ((SWAP_LR S U (§#§))-o--|c31,ID|--o-(SWAP_LS T (§#§) U)-o--|ID,c32|--o-RSH ).
Proof.
introv H2 H1.
destruct H1 as [H1|[H1|H1]].
- apply ttrs0_imp_ttrg0_d2 in H2.
  left. constructor; easy.
- apply ttrs0_imp_ttrg0_d3 in H2.
  right. left. constructor; easy.
- apply ttrs0_imp_ttrg0_kB in H2.
  right. right. constructor; easy.
Qed.

(** A safe or corrupted state can be considered as a potentially more corrupted state *)

Lemma ttrg0_d1_imp_d1kA : forall S T (c c':circuit S T) c3, ttrg0_d1 c c' c3 -> ttrg0_d1kA c c' c3.
Proof.
induction c; introv H; Inverts H; try constructor; 
             try (apply IHc1; easy); try (apply IHc2; easy).
- apply IHc in H6. easy.
- Inverts H7. constructor. 
Qed.

Lemma ttrs0_imp_ttrg0_d1kA : forall S T (c c':circuit S T) c3, ttrs0 c c' c3 -> ttrg0_d1kA c c' c3.
Proof.
induction c; introv H; Inverts H; try constructor; 
             try (apply IHc1; easy); try (apply IHc2; easy).
- apply IHc in H6. easy. 
- Inverts H7. constructor. 
Qed.

(** Lemmas on ttrg1 relations *)
Lemma ttrg1_d2d3kB_lseq : forall S T U (c1 c1':circuit S T) (c2 c2':circuit T U) c31 c32,
                          ttrs1 c2 c2' c32 
                       -> ttrg1_d2d3kB c1 c1' c31
                       -> ttrg1_d2d3kB (c1-o-c2) (c1'-o-c2') (c31-o-c32).
Proof.
introv H2 H1.
destruct H1 as [H1|[H1|H1]].
- apply ttrs1_imp_ttrg1_d2 in H2.
  left. constructor; easy.
- apply ttrs1_imp_ttrg1_d3 in H2.
  right. left. constructor; easy.
- apply ttrs1_imp_ttrg1_kB in H2.
  right. right. constructor; easy.
Qed.

Lemma ttrg1_d2d3kB_rseq : forall S T U (c1 c1':circuit S T) (c2 c2':circuit T U) c31 c32,
                          ttrs1 c1 c1' c31 
                       -> ttrg1_d2d3kB c2 c2' c32
                       -> ttrg1_d2d3kB (c1-o-c2) (c1'-o-c2') (c31-o-c32).
Proof.
introv H2 H1.
destruct H1 as [H1|[H1|H1]].
- apply ttrs1_imp_ttrg1_d2 in H2.
  left. constructor; easy.
- apply ttrs1_imp_ttrg1_d3 in H2.
  right. left. constructor; easy.
- apply ttrs1_imp_ttrg1_kB in H2.
  right. right. constructor; easy.
Qed.

Lemma ttrg1_d2d3kB_lpar : forall S T U V (c1 c1':circuit S T) (c2 c2':circuit U V) c31 c32,
                          ttrs1 c2 c2' c32 
                       -> ttrg1_d2d3kB c1 c1' c31
                       -> ttrg1_d2d3kB (-|c1,c2|-) (-|c1',c2'|-) 
                             ((SWAP_LR S U (§#§))-o--|c31,ID|--o-(SWAP_LS T (§#§) U)-o--|ID,c32|--o-RSH ).
Proof.
introv H2 H1.
destruct H1 as [H1|[H1|H1]].
- apply ttrs1_imp_ttrg1_d2 in H2.
  left. constructor; easy.
- apply ttrs1_imp_ttrg1_d3 in H2.
  right. left. constructor; easy.
- apply ttrs1_imp_ttrg1_kB in H2.
  right. right. constructor; easy.
Qed.

Lemma ttrg1_d2d3kB_rpar : forall S T U V (c1 c1':circuit S T) (c2 c2':circuit U V) c31 c32,
                          ttrs1 c1 c1' c31 
                       -> ttrg1_d2d3kB c2 c2' c32 
                       -> ttrg1_d2d3kB (-|c1,c2|-) (-|c1',c2'|-) 
                          ((SWAP_LR S U (§#§))-o--|c31,ID|--o-(SWAP_LS T (§#§) U)-o--|ID,c32|--o-RSH ).
Proof.
introv H2 H1.
destruct H1 as [H1|[H1|H1]].
- apply ttrs1_imp_ttrg1_d2 in H2.
  left. constructor; easy.
- apply ttrs1_imp_ttrg1_d3 in H2.
  right. left. constructor; easy.
- apply ttrs1_imp_ttrg1_kB in H2.
  right. right. constructor; easy.
Qed.

Lemma ttrg1_d1_imp_d1kA : forall S T (c c':circuit S T) c3, ttrg1_d1 c c' c3 -> ttrg1_d1kA c c' c3.
Proof.
induction c; introv H; Inverts H; try constructor; 
             try (apply IHc1; easy); try (apply IHc2; easy).
- apply IHc in H6. easy. 
- Inverts H7. constructor. 
Qed.

Lemma ttrs1_imp_ttrg1_d1kA : forall S T (c c':circuit S T) c3, ttrs1 c c' c3 -> ttrg1_d1kA c c' c3.
Proof.
induction c; introv H; Inverts H; try constructor; 
             try (apply IHc1; easy); try (apply IHc2; easy).
- apply IHc in H6. easy. 
- Inverts H7. constructor. 
Qed.

(** Lemmas on ttrg2 relations *)
Lemma ttrg2_d2d3kB_lseq : forall S T U (c1 c1':circuit S T) (c2 c2':circuit T U) c31 c32,
                          ttrs2 c2 c2' c32 
                       -> ttrg2_d2d3kB c1 c1' c31 
                       -> ttrg2_d2d3kB (c1-o-c2) (c1'-o-c2') (c31-o-c32).
Proof.
introv H2 H1.
destruct H1 as [H1|[H1|H1]].
- apply ttrs2_imp_ttrg2_d2 in H2.
  left. constructor; easy.
- apply ttrs2_imp_ttrg2_d3 in H2.
  right. left. constructor; easy.
- apply ttrs2_imp_ttrg2_kB in H2.
  right. right. constructor; easy.
Qed.

Lemma ttrg2_d2d3kB_rseq : forall S T U (c1 c1':circuit S T) (c2 c2':circuit T U) c31 c32,
                          ttrs2 c1 c1' c31 
                       -> ttrg2_d2d3kB c2 c2' c32
                       -> ttrg2_d2d3kB (c1-o-c2) (c1'-o-c2') (c31-o-c32).
Proof.
introv H2 H1.
destruct H1 as [H1|[H1|H1]].
- apply ttrs2_imp_ttrg2_d2 in H2.
  left. constructor; easy.
- apply ttrs2_imp_ttrg2_d3 in H2.
  right. left. constructor; easy.
- apply ttrs2_imp_ttrg2_kB in H2.
  right. right. constructor; easy.
Qed.

Lemma ttrg2_d2d3kB_lpar : forall S T U V (c1 c1':circuit S T) (c2 c2':circuit U V) c31 c32,
                          ttrs2 c2 c2' c32 
                       -> ttrg2_d2d3kB c1 c1' c31  
                       -> ttrg2_d2d3kB (-|c1,c2|-) (-|c1',c2'|-) 
                         ((SWAP_LR S U (§#§))-o--|c31,ID|--o-(SWAP_LS T (§#§) U)-o--|ID,c32|--o-RSH ).
Proof.
introv H2 H1.
destruct H1 as [H1|[H1|H1]].
- apply ttrs2_imp_ttrg2_d2 in H2.
  left. constructor; easy.
- apply ttrs2_imp_ttrg2_d3 in H2.
  right. left. constructor; easy.
- apply ttrs2_imp_ttrg2_kB in H2.
  right. right. constructor; easy.
Qed.

Lemma ttrg2_d2d3kB_rpar : forall S T U V (c1 c1':circuit S T) (c2 c2':circuit U V) c31 c32,
                          ttrs2 c1 c1' c31 
                       -> ttrg2_d2d3kB c2 c2' c32 
                       -> ttrg2_d2d3kB (-|c1,c2|-) (-|c1',c2'|-) 
                           ((SWAP_LR S U (§#§))-o--|c31,ID|--o-(SWAP_LS T (§#§) U)-o--|ID,c32|--o-RSH ).
Proof.
introv H2 H1.
destruct H1 as [H1|[H1|H1]].
- apply ttrs2_imp_ttrg2_d2 in H2.
  left. constructor; easy.
- apply ttrs2_imp_ttrg2_d3 in H2.
  right. left. constructor; easy.
- apply ttrs2_imp_ttrg2_kB in H2.
  right. right. constructor; easy.
Qed.


Lemma ttrg2_d1_imp_d1kA : forall S T (c c':circuit S T) c3, ttrg2_d1 c c' c3 -> ttrg2_d1kA c c' c3.
Proof.
induction c; introv H; Inverts H; try constructor; 
             try (apply IHc1; easy); try (apply IHc2; easy).
- apply IHc in H6. easy.
- Inverts H7. constructor. 
Qed.

Lemma ttrs2_imp_ttrg2_d1kA : forall S T (c c':circuit S T) c3, ttrs2 c c' c3 -> ttrg2_d1kA c c' c3.
Proof.
induction c; introv H; Inverts H; try constructor; 
             try (apply IHc1; easy); try (apply IHc2; easy).
- apply IHc in H6. easy. 
- Inverts H7. constructor. 
Qed.

(** * Lemmas on reduction with glitch within a triplicated circuit             *)

(** A glitch in a triplicated circuit does not contaminate the control signals *)

Lemma ttrs_stepg : forall S T (c c':circuit S T) (c3 c3':circuit (S#(§#§)) (T#(§#§))) smb s t f f', 
                   ttrs smb c c' c3
                -> stepg c3 {s,f} {t,f'} c3'
                -> f = f'.
Proof.
induction c'; introv R G; Inverts R.
- Invstep G. SimpS; easy. 
- Invstep G. SimpS; easy.
- Inverts G; Dd_buset t0. 
  + Apply IHc'1 with H4 in H3.
    Apply ttr_step_fAB with H7 in H10. subst. easy. 
  + Apply ttr_step_fAB with H4 in H3.
    Apply IHc'2 with H7 in H10. subst. easy.
- Dd_buset s. Dd_buset t.
  apply invstepgTTRpar in G. 
  destruct G as [[fAB [c31' [c32' [G1 [G2 G3]]]]] | 
                 [fAB [c31' [c32' [G1 [G2 G3]]]]] ].
  + Apply IHc'1 with H2 in G1.
    Apply ttr_step_fAB with H8 in G2.
    subst. easy.
  + Apply ttr_step_fAB with H2 in G1. 
    Apply IHc'2 with H8 in G2.
    subst. easy.
- unfold SWAP_LR in G. unfold SWAP_LS in G. 
  Invstep G.
  + Apply ttr_step_fAB with H5 in H8.
    Apply fact_stepg_mb in H1. 
    SimpS. easy. 
  + Apply IHc' with H5 in H1.
    Apply fact0_mb_ttr  in H2. 
    SimpS. easy. 
  + Apply ttr_step_fAB with H5 in H9.
    Apply fact0_mb_ttr in H12. 
    SimpS. easy.
Qed.
 

(** Effect of a glitch in a triplicated circuit in state ttrs0 *)

Lemma stepgl_ttrs0 : forall S T (x c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                     pure_bset s 
                  -> step c s t c' 
                  -> ttrs0 x c c3
                  -> stepglitch c3 {s,{~1,~1}} t' c3' 
                 ->  ttrg1_d1kA c c' c3' \/ (t'={t,{~1,~1}} /\ ttrg1_d2d3kB c c' c3').
Proof. 
introv P G R H.
induction c; Inverts G; Inverts R.
- apply stepglitch_comb_cir in H; try easy.
  subst. left. constructor. 
- apply stepglitch_comb_cir in H; try easy. 
  subst. left. constructor. 
- Purestep H4. Inverts H.
  + Inverts H11. Inverts H8.
    * Apply ttrs0_step_s with H6 H4 in H3. SimpS. 
      Apply ttrs0_step_s with H10 H9 in H14. SimpS.
      apply ttrg1_d1_imp_d1kA in H1.
      apply ttrg1_d1_imp_d1kA in H2.
      left. constructor; easy.
   * Inverts H0.  
   { Apply ttrs0_step_fA with H6 H4 in H3. SimpS. 
     Apply ttrs0_step_fA with H10 H9 in H14. SimpS.
     constructor; apply ttrs1_imp_ttrg1_d1kA; easy. }
   { Apply ttrs0_step_fB with H6 H4 in H3. SimpS.
     Apply ttrs0_step_fB with H10 H9 in H14. SimpS.
     constructor; apply ttrs1_imp_ttrg1_d1kA; easy. }
   { Apply ttrs0_step_s  with H6 H4 in H3. SimpS. 
     Apply ttrs0_step_s with H10 H9 in H14. SimpS.
     apply ttrg1_d1_imp_d1kA in H0. 
     apply ttrg1_d1_imp_d1kA in H1.
     repeat constructor; easy. }
   * Apply ttrs0_step_s  with H6 H4 in H3. SimpS. 
     Apply ttrs0_step_s with H10 H9 in H14. SimpS.
     apply ttrg1_d1_imp_d1kA in H1.
     apply ttrg1_d1_imp_d1kA in H0.
     left. constructor; easy.
  + Inverts H8.
    * dupl H3 X. Dd_buset t1.
      Apply ttrs_stepg with H6 in X.
      apply stepg_imp_stepglitch in H3.
      Apply IHc1 with H4 H6 in H3.
      SimpS. destruct H3 as [R1|[X R1]].
      { left. Apply ttrs0_step_s with H9 H13 H10 in H13. 
        destruct H13 as [X R2]. apply ttrg1_d1_imp_d1kA in R2.
        constructor; easy. }
      { right. SimpS. 
        Apply ttrs0_step with H9 H13 in H10. SimpS.
        Simpl. split. easy. apply ttrg1_d2d3kB_lseq; easy. }
    * Apply step_ttrs0 with H6 in H4. SimpS. Rdet. SimpS.
      apply stepg_imp_stepglitch in H13. SimpS.
      Apply IHc2 with H9 H10 in H13.
      destruct H13 as [?|[? ?]].
     { left. apply ttrs1_imp_ttrg1_d1kA in H0. constructor; easy. }
     { right. SimpS. split. easy. apply ttrg1_d2d3kB_rseq; easy. } 
- Inverts H; SimpS.
  + apply invstepTTRpar in H9. destruct H9 as [?[?[?[?[?[H9 H7]]]]]].
    Inverts H8; SimpS. 
    * Apply ttrs0_step_s with H4 H9 in H3. SimpS.
      Apply ttrs0_step_s with H7 H11 in H10. SimpS.
      left. constructor; apply ttrg1_d1_imp_d1kA; easy. 
    * Inverts H5.
      { Apply ttrs0_step_fA with H4 H9 in H3. SimpS.
        Apply ttrs0_step_fA with H7 H11 in H10. SimpS.
        left. constructor; apply ttrs1_imp_ttrg1_d1kA; easy. }
      { Apply ttrs0_step_fB with H4 H9 in H3. SimpS.
        Apply ttrs0_step_fB with H7 H11 in H10. SimpS.
        left. constructor; apply ttrs1_imp_ttrg1_d1kA; easy. }
      { Simpl. Apply ttrs0_step_s with H4 H9 in H3. SimpS.
        Apply ttrs0_step_s with H7 H11 in H10. SimpS.
        left. constructor; apply ttrg1_d1_imp_d1kA; easy. }
    * Apply ttrs0_step_s with H9 H4 in H3. SimpS.
      Apply ttrs0_step_s with H7 H11 in H10. SimpS. 
      left. constructor; apply ttrg1_d1_imp_d1kA; easy. 
  + apply invstepgTTRpar in H8. 
    destruct H8 as [[fAB [c31' [c32' [G1 [G2 G3]]]]] | 
                    [fAB [c31' [c32' [G1 [G2 G3]]]]] ]; subst.
    * dupl G1 X. Apply ttrs_stepg with H4 in X. subst.
      apply stepg_imp_stepglitch in G1. 
      Apply IHc1 with H3 H4 in G1.
      destruct G1 as [R1 | [X G1]].
      { Apply ttrs0_step_s with H11 G2 in H10. SimpS.
        left. apply ttrg1_d1_imp_d1kA in H2. constructor; easy. }
      { Apply ttrs0_step with H11 G2 in H10. SimpS.
        right. constructor. easy. apply ttrg1_d2d3kB_lpar; easy. }
    * Apply ttrs0_step with H4 G1 in H3. SimpS.
      apply stepg_imp_stepglitch in G2. 
      Apply IHc2 with H10 H11 in G2.
      destruct G2 as [R2 | [X R2]].
      { left. apply ttrs1_imp_ttrg1_d1kA in H2. constructor; easy. }
      { SimpS. right. split. easy.
        apply ttrg1_d2d3kB_rpar; easy. }
- Inverts H9. Inverts H; SimpS.
  + apply invstepTTRloop in H10. 
    destruct H10 as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
    Inverts H9; SimpS.
    * apply step0_mb_ttr1 in G4. destruct G4 as [X [b1 [? ?]]]. Simpl.
      Apply ttrs0_step_s with H6 H8 in G3. SimpS.
      left. constructor. apply ttrg1_d1_imp_d1kA. easy. constructor.
    * Inverts H0.
      { apply step0_mb_ttr4 in G4. Simpl.
        Apply ttrs0_step_fA with H6 H8 in G3. SimpS.
        left. repeat constructor. apply ttrs1_imp_ttrg1_d1kA; easy. }
      { apply step0_mb_ttr5 in G4. Simpl.
        Apply ttrs0_step_fB with H6 H8 in G3. SimpS.
        left. repeat constructor. apply ttrs1_imp_ttrg1_d1kA; easy. }
      { SimpS. apply step0_mb_ttr4 in G4. SimpS.
        Apply ttrs0_step_s with H6 H8 in G3. SimpS.
        left. repeat constructor. apply ttrg1_d1_imp_d1kA; easy. }
    * apply step0_mb_ttr4 in G4. SimpS.
      Apply ttrs0_step_s  with H6 H8 in G3. SimpS.
      left. repeat constructor. apply ttrg1_d1_imp_d1kA in H0; easy.
  + eapply invstepgTTRloop0 in H9.
    destruct H9 as [ [t1 [b1 [c31 [H [? ?]]]]] | 
                   [ [a0 [b0 [z [c1' [m [G1 [G2 [G3 G4]]]]]]]] |
                     [a0 [b0 [z [c1' [m [G1 [G2 G3]]]]]]]]]; subst.
    * apply stepg_imp_stepglitch in H. 
      Apply IHc with H8 H6 in H.
      destruct H as [R|[X R]]. 
      { left. repeat constructor; easy. } 
      { Simpl. right. split. easy. destruct R as [R|[R|R]].
        - left. repeat constructor. exact R.
        - right. left. repeat constructor. exact R.
        - right. right. repeat constructor. exact R. }
    * Apply ttrs0_step with H6 H8 in G1. Simpl. 
      destruct G4 as [G4|[G4|G4]]; subst.
      { right. split. easy.
        repeat constructor. apply ttrs1_imp_ttrg1_d2; easy. }
      { right. split. easy.
        right. left. repeat constructor. apply ttrs1_imp_ttrg1_d3; easy. }
      { right. split. easy.
       right. right. repeat constructor. apply ttrs1_imp_ttrg1_kB; easy. }
    * Apply ttrs0_step_s with H6 H8 in G1. SimpS.
      left. repeat constructor. apply ttrg1_d1_imp_d1kA; easy.
Qed.

(** Effect of a glitch in a triplicated circuit in state ttrs1 *)


Lemma stepgl_ttrs1 : forall S T (c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                     pure_bset s 
                  -> step c s t c' 
                  -> ttrs1 c c' c3
                  -> stepglitch c3 {s,{~0,~0}} t' c3' 
                 ->  ttrg2_d1kA c c' c3' \/ (t'={t,{~0,~0}} /\ ttrg2_d2d3kB c c' c3').
Proof. 
introv P G R H.
induction c; Inverts G; Inverts R.
- apply stepglitch_comb_cir in H; try easy.
  subst. left. constructor. 
- apply stepglitch_comb_cir in H; try easy. 
  subst. left. constructor. 
- Purestep H4. Inverts H.
  + Inverts H10. Inverts H8.
    * Apply ttrs1_step_s with H5 H3 in H4. SimpS. 
      Apply ttrs1_step_s with H11 H9 in H14. SimpS.
      apply ttrg2_d1_imp_d1kA in H1.
      apply ttrg2_d1_imp_d1kA in H2.
      left. constructor; easy.
   * Inverts H0.  
   { Apply ttrs1_step_fA with H5 H4 in H3. SimpS. 
     Apply ttrs1_step_fA with H11 H9 in H14. SimpS.
     constructor; apply ttrs2_imp_ttrg2_d1kA; easy. }
   { Apply ttrs1_step_fB with H5 H4 in H3. SimpS.
     Apply ttrs1_step_fB with H11 H9 in H14. SimpS.
     constructor; apply ttrs2_imp_ttrg2_d1kA; easy. }
   { Apply ttrs1_step_s  with H5 H4 in H3. SimpS. 
     Apply ttrs1_step_s with H11 H9 in H14. SimpS.
     apply ttrg2_d1_imp_d1kA in H0. 
     apply ttrg2_d1_imp_d1kA in H1.
     repeat constructor; easy. }
   * Apply ttrs1_step_s with H5 H4 in H3. SimpS. 
     Apply ttrs1_step_s with H11 H9 in H14. SimpS.
     apply ttrg2_d1_imp_d1kA in H1.
     apply ttrg2_d1_imp_d1kA in H0.
     left. constructor; easy.
  + Inverts H8.
    * dupl H3 X. Dd_buset t1.
      Apply ttrs_stepg with H5 in X.
      apply stepg_imp_stepglitch in H3.
      Apply IHc1 with H4 H5 in H3.
      SimpS. destruct H3 as [R1|[X R1]].
      { left. Apply ttrs1_step_s with H9 H13 H11 in H13. 
        destruct H13 as [X R2]. apply ttrg2_d1_imp_d1kA in R2.
        constructor; easy. }
      { right. SimpS. 
        Apply ttrs1_step with H9 H13 in H11. SimpS.
        Simpl. split. easy. apply ttrg2_d2d3kB_lseq; easy. }
    * Apply step_ttrs1 with H5 in H4. SimpS. Rdet. SimpS.
      apply stepg_imp_stepglitch in H13. SimpS.
      Apply IHc2 with H9 H11 in H13.
      destruct H13 as [?|[? ?]].
     { left. apply ttrs2_imp_ttrg2_d1kA in H0. constructor; easy. }
     { right. SimpS. split. easy. apply ttrg2_d2d3kB_rseq; easy. } 
- Inverts H; SimpS.
  + apply invstepTTRpar in H9. destruct H9 as [?[?[?[?[?[H9 H7]]]]]].
    Inverts H8; SimpS. 
    * Apply ttrs1_step_s with H4 H9 in H3. SimpS.
      Apply ttrs1_step_s with H7 H12 in H10. SimpS.
      left. constructor; apply ttrg2_d1_imp_d1kA; easy. 
    * Inverts H5.
      { Apply ttrs1_step_fA with H4 H9 in H3. SimpS.
        Apply ttrs1_step_fA with H7 H12 in H10. SimpS.
        left. constructor; apply ttrs2_imp_ttrg2_d1kA; easy. }
      { Apply ttrs1_step_fB with H4 H9 in H3. SimpS.
        Apply ttrs1_step_fB with H7 H12 in H10. SimpS.
        left. constructor; apply ttrs2_imp_ttrg2_d1kA; easy. }
      { Simpl. Apply ttrs1_step_s with H4 H9 in H3. SimpS.
        Apply ttrs1_step_s with H7 H12 in H10. SimpS.
        left. constructor; apply ttrg2_d1_imp_d1kA; easy. }
    * Apply ttrs1_step_s with H9 H4 in H3. SimpS.
      Apply ttrs1_step_s with H7 H12 in H10. SimpS. 
      left. constructor; apply ttrg2_d1_imp_d1kA; easy. 
  + apply invstepgTTRpar in H8. 
    destruct H8 as [[fAB [c31' [c32' [G1 [G2 G3]]]]] | 
                    [fAB [c31' [c32' [G1 [G2 G3]]]]] ]; subst.
    * dupl G1 X. Apply ttrs_stepg with H4 in X. subst.
      apply stepg_imp_stepglitch in G1. 
      Apply IHc1 with H3 H4 in G1.
      destruct G1 as [R1 | [X G1]].
      { Apply ttrs1_step_s with H12 G2 in H10. SimpS.
        left. apply ttrg2_d1_imp_d1kA in H2. constructor; easy. }
      { Apply ttrs1_step with H12 G2 in H10. SimpS.
        right. constructor. easy. apply ttrg2_d2d3kB_lpar; easy. }
    * Apply ttrs1_step with H4 G1 in H3. SimpS.
      apply stepg_imp_stepglitch in G2. 
      Apply IHc2 with H10 H12 in G2.
      destruct G2 as [R2 | [X R2]].
      { left. apply ttrs2_imp_ttrg2_d1kA in H2. constructor; easy. }
      { SimpS. right. split. easy.
        apply ttrg2_d2d3kB_rpar; easy. }
- Inverts H10. Inverts H; SimpS.
  + apply invstepTTRloop in H10. 
    destruct H10 as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
    Inverts H9; SimpS.
    * apply step1_mb_ttr1 in G4. destruct G4 as [X [b1 [? ?]]]. Simpl.
      Apply ttrs1_step_s with H8 in G3. SimpS.
      left. constructor. apply ttrg2_d1_imp_d1kA. easy. constructor.
    * Inverts H0.
      { apply step1_mb_ttr4 in G4. Simpl.
        Apply ttrs1_step_fA with H8 in G3. SimpS.
        left. repeat constructor. apply ttrs2_imp_ttrg2_d1kA; easy. }
      { apply step1_mb_ttr5 in G4. Simpl.
        Apply ttrs1_step_fB with H8 in G3. SimpS.
        left. repeat constructor. apply ttrs2_imp_ttrg2_d1kA; easy. }
      { SimpS. apply step1_mb_ttr4 in G4. SimpS.
        Apply ttrs1_step_s with H5 H8 in G3. SimpS.
        left. repeat constructor. apply ttrg2_d1_imp_d1kA; easy. }
    * apply step1_mb_ttr4 in G4. SimpS.
      Apply ttrs1_step_s  with H5 H8 in G3. SimpS.
      left. repeat constructor. apply ttrg2_d1_imp_d1kA in H0; easy.
  + eapply invstepgTTRloop1 in H9.
    destruct H9 as [ [t1 [b1 [c31 [H [? ?]]]]] | 
                   [ [a0 [b0 [z [c1' [m [G1 [G2 [G3 G4]]]]]]]] |
                     [a0 [b0 [z [c1' [m [G1 [G2 G3]]]]]]]]]; subst.
    * apply stepg_imp_stepglitch in H. 
      Apply IHc with H8 H5 in H.
      destruct H as [R|[X R]]. 
      { left. repeat constructor; easy. } 
      { Simpl. right. split. easy. destruct R as [R|[R|R]].
        - left. repeat constructor. exact R.
        - right. left. repeat constructor. exact R.
        - right. right. repeat constructor. exact R. }
    * Apply ttrs1_step with H5 H8 in G1. Simpl. 
      destruct G4 as [G4|[G4|G4]]; subst.
      { right. split. easy.
        repeat constructor. apply ttrs2_imp_ttrg2_d2; easy. }
      { right. split. easy.
        right. left. repeat constructor. apply ttrs2_imp_ttrg2_d3; easy. }
      { right. split. easy.
       right. right. repeat constructor. apply ttrs2_imp_ttrg2_kB; easy. }
    * Apply ttrs1_step_s with H5 H8 in G1. SimpS.
      left. repeat constructor. apply ttrg2_d1_imp_d1kA; easy.
Qed.


(** Effect of a glitch in a triplicated circuit in state ttrs2 *)

Lemma stepgl_ttrs2 : forall S T (c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                     pure_bset s 
                  -> step c s t c'
                  -> ttrs2 c c' c3
                  -> stepglitch c3 {s,{~0,~0}} t' c3' 
                  -> ttrg0_d1kA c c' c3' \/ (t'={t,{~0,~0}} /\ ttrg0_d2d3kB c c' c3').
Proof. 
introv P G R H.
induction c; Inverts G; Inverts R.
- apply stepglitch_comb_cir in H; try easy.
  subst. left. constructor. 
- apply stepglitch_comb_cir in H; try easy. 
  subst. left. constructor. 
- Purestep H4. Inverts H.
  + Inverts H10. Inverts H8.
    * Apply ttrs2_step_s with H5 H3 in H4. SimpS. 
      Apply ttrs2_step_s with H11 H9 in H14. SimpS.
      apply ttrg0_d1_imp_d1kA in H1.
      apply ttrg0_d1_imp_d1kA in H2.
      left. constructor; easy.
   * Inverts H0.  
   { Apply ttrs2_step_fA with H5 H4 in H3. SimpS. 
     Apply ttrs2_step_fA with H11 H9 in H14. SimpS.
     constructor; apply ttrs0_imp_ttrg0_d1kA; easy. }
   { Apply ttrs2_step_fB with H5 H4 in H3. SimpS.
     Apply ttrs2_step_fB with H11 H9 in H14. SimpS.
     constructor; apply ttrs0_imp_ttrg0_d1kA; easy. }
   { Apply ttrs2_step_s  with H5 H4 in H3. SimpS. 
     Apply ttrs2_step_s with H11 H9 in H14. SimpS.
     apply ttrg0_d1_imp_d1kA in H0. 
     apply ttrg0_d1_imp_d1kA in H1.
     repeat constructor; easy. }
   * Apply ttrs2_step_s with H5 H4 in H3. SimpS. 
     Apply ttrs2_step_s with H11 H9 in H14. SimpS.
     apply ttrg0_d1_imp_d1kA in H1.
     apply ttrg0_d1_imp_d1kA in H0.
     left. constructor; easy.
  + Inverts H8.
    * dupl H3 X. Dd_buset t1.
      Apply ttrs_stepg with H5 in X.
      apply stepg_imp_stepglitch in H3.
      Apply IHc1 with H4 H5 in H3.
      SimpS. destruct H3 as [R1|[X R1]].
      { left. Apply ttrs2_step_s with H9 H13 H11 in H13. 
        destruct H13 as [X R2]. apply ttrg0_d1_imp_d1kA in R2.
        constructor; easy. }
      { right. SimpS. 
        Apply ttrs2_step with H9 H13 in H11. SimpS.
        Simpl. split. easy. apply ttrg0_d2d3kB_lseq; easy. }
    * Apply step_ttrs2 with H5 in H4. SimpS. Rdet. SimpS.
      apply stepg_imp_stepglitch in H13. SimpS.
      Apply IHc2 with H9 H11 in H13.
      destruct H13 as [?|[? ?]].
     { left. apply ttrs0_imp_ttrg0_d1kA in H0. constructor; easy. }
     { right. SimpS. split. easy. apply ttrg0_d2d3kB_rseq; easy. } 
- Inverts H; SimpS.
  + apply invstepTTRpar in H9. destruct H9 as [?[?[?[?[?[H9 H7]]]]]].
    Inverts H8; SimpS. 
    * Apply ttrs2_step_s with H4 H9 in H3. SimpS.
      Apply ttrs2_step_s with H7 H12 in H10. SimpS.
      left. constructor; apply ttrg0_d1_imp_d1kA; easy. 
    * Inverts H5.
      { Apply ttrs2_step_fA with H4 H9 in H3. SimpS.
        Apply ttrs2_step_fA with H7 H12 in H10. SimpS.
        left. constructor; apply ttrs0_imp_ttrg0_d1kA; easy. }
      { Apply ttrs2_step_fB with H4 H9 in H3. SimpS.
        Apply ttrs2_step_fB with H7 H12 in H10. SimpS.
        left. constructor; apply ttrs0_imp_ttrg0_d1kA; easy. }
      { Simpl. Apply ttrs2_step_s with H4 H9 in H3. SimpS.
        Apply ttrs2_step_s with H7 H12 in H10. SimpS.
        left. constructor; apply ttrg0_d1_imp_d1kA; easy. }
    * Apply ttrs2_step_s with H9 H4 in H3. SimpS.
      Apply ttrs2_step_s with H7 H12 in H10. SimpS. 
      left. constructor; apply ttrg0_d1_imp_d1kA; easy. 
  + apply invstepgTTRpar in H8. 
    destruct H8 as [[fAB [c31' [c32' [G1 [G2 G3]]]]] | 
                    [fAB [c31' [c32' [G1 [G2 G3]]]]] ]; subst.
    * dupl G1 X. Apply ttrs_stepg with H4 in X. subst.
      apply stepg_imp_stepglitch in G1. 
      Apply IHc1 with H3 H4 in G1.
      destruct G1 as [R1 | [X G1]].
      { Apply ttrs2_step_s with H12 G2 in H10. SimpS.
        left. apply ttrg0_d1_imp_d1kA in H2. constructor; easy. }
      { Apply ttrs2_step with H12 G2 in H10. SimpS.
        right. constructor. easy. apply ttrg0_d2d3kB_lpar; easy. }
    * Apply ttrs2_step with H4 G1 in H3. SimpS.
      apply stepg_imp_stepglitch in G2. 
      Apply IHc2 with H10 H12 in G2.
      destruct G2 as [R2 | [X R2]].
      { left. apply ttrs0_imp_ttrg0_d1kA in H2. constructor; easy. }
      { SimpS. right. split. easy.
        apply ttrg0_d2d3kB_rpar; easy. }
- Inverts H10. Inverts H; SimpS.
  + apply invstepTTRloop in H10. 
    destruct H10 as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
    Inverts H9; SimpS.
    * apply step1_mb_ttr1 in G4. destruct G4 as [X [b1 [? ?]]]. Simpl.
      Apply ttrs2_step_s with H8 in G3. SimpS.
      left. constructor. apply ttrg0_d1_imp_d1kA. easy. constructor.
    * Inverts H0.
      { apply step1_mb_ttr4 in G4. Simpl.
        Apply ttrs2_step_fA with H8 in G3. SimpS.
        left. repeat constructor. apply ttrs0_imp_ttrg0_d1kA; easy. }
      { apply step1_mb_ttr5 in G4. Simpl.
        Apply ttrs2_step_fB with H8 in G3. SimpS.
        left. repeat constructor. apply ttrs0_imp_ttrg0_d1kA; easy. }
      { SimpS. apply step1_mb_ttr4 in G4. SimpS.
        Apply ttrs2_step_s with H5 H8 in G3. SimpS.
        left. repeat constructor. apply ttrg0_d1_imp_d1kA; easy. }
    * apply step1_mb_ttr4 in G4. SimpS.
      Apply ttrs2_step_s  with H5 H8 in G3. SimpS.
      left. repeat constructor. apply ttrg0_d1_imp_d1kA in H0; easy.
  + eapply invstepgTTRloop2 in H9.
    destruct H9 as [ [t1 [b1 [c31 [H [? ?]]]]] | 
                   [ [a0 [b0 [z [c1' [m [G1 [G2 [G3 G4]]]]]]]] |
                     [a0 [b0 [z [c1' [m [G1 [G2 G3]]]]]]]]]; subst.
    * apply stepg_imp_stepglitch in H. 
      Apply IHc with H8 H5 in H.
      destruct H as [R|[X R]]. 
      { left. repeat constructor; easy. } 
      { Simpl. right. split. easy. destruct R as [R|[R|R]].
        - left. repeat constructor. exact R.
        - right. left. repeat constructor. exact R.
        - right. right. repeat constructor. exact R. }
    * Apply ttrs2_step with H5 H8 in G1. Simpl. 
      destruct G4 as [G4|[G4|G4]]; subst.
      { right. split. easy.
        repeat constructor. apply ttrs0_imp_ttrg0_d2; easy. }
      { right. split. easy.
        right. left. repeat constructor. apply ttrs0_imp_ttrg0_d3; easy. }
      { right. split. easy.
       right. right. repeat constructor. apply ttrs0_imp_ttrg0_kB; easy. }
    * Apply ttrs2_step_s with H5 H8 in G1. SimpS.
      left. repeat constructor. apply ttrg0_d1_imp_d1kA; easy.
Qed.
