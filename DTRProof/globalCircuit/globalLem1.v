(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation
#</h1>#
- Lemmas used for the global proof of glitch occurring in cycles 0

          Dmitry Burlyaev - Pascal Fradet - 2015

#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".
Add LoadPath "..\controlBlock\".
Add LoadPath "..\inputBuffers\".
Add LoadPath "..\outputBuffers\".
Add LoadPath "..\memoryBlocks\".

Require Import dtrTransform relationPred.
Require Import globalInv globalStep globalSeqs.
Require Import inputLib controlLib outputLib memoryLib.

Set Implicit Arguments.

(* ------------------------------------------------------- *)

Lemma glitch_in_3fail : forall S T (i0 i1 i2 i3 i4 i5: {|S|})
                           (o0 o1 o2 o3 o4 o5: {|T|})
                           (oo1 oo2 oo3 oo4 oo5 oo6 oo7 oo8 oo9:{|T # (T # T)|})
                           (c0 c1 c2 c3 c4 c5 c6: circuit S T)
                           (cc2' cc3 cc3' cc4 cc4' cc5 cc5' cc6: circuit S (T # (T # T)))
                            a a0 a1 b' b'0 b'1 bg c' cc,
                pure_bset {i0,i1,i2,i3,i4,i5,o0,o1,o2,o3,o4,o5}
             -> dtrs1 c0 c1 c2 cc
             -> bset2bool a b' -> bset2bool a0 b'0 -> bset2bool a1 b'1
             -> introglitch (bool2bset false) bg
             -> step c1 i1 o1 c2
             -> step c2 i2 o2 c3
             -> step c3 i3 o3 c4
             -> step c4 i4 o4 c5
             -> step c5 i5 o5 c6
             -> step (-{ b' }- (-{ b'0 }- (-{ b'1 }- c'))) i2 oo2 cc2'
             -> step  cc2' i2 oo3 cc3
             -> step  cc3  i3 oo4 cc3'
             -> step  cc3' i3 oo5 cc4
             -> step  cc4  i4 oo6 cc4'
             -> step  cc4' i4 oo7 cc5
             -> step  cc5  i5 oo8 cc5'
             -> step  cc5' i5 oo9 cc6
             -> step (dtrcore (ibs1 i1 i0) cbs1 cc (obs1 o1 o0)) {i1, bool2bset false, bool2bset false, bg}
                                                                {oo1, a, a0, a1} c'
             -> atleast2 o0 oo1
             /\ atleast2 o1 oo3
             /\ atleast2 o2 oo5
             /\ atleast2 o3 oo7
             /\ atleast2 o4 oo9
             /\ Dtrs0 (ibs0 i5) (obs0 o5 o4) c5 c6 cc6.
Proof.
  introv P D B1 B2 B3 I.
  introv S2 S3 S4 S5 S6.
  introv SS2 SS3 SS4 SS5 SS6 SS7 SS8 SS9.
  introv H. SimpS.
  Apply invstepcore in H. unfold PexInvDTR1 in H. SimpS.
  Inverts I.
  - eapply step1_tcbv_i in H12; try (solve [constructor]). SimpS.
    Apply step_ibs in H; try apply pure_buildBus. SimpS. Purestep H13.
    Apply step1_mb with D S2 in H13. SimpS. Purestep H14. SimpS.
    Apply step_obs_sf in H14. SimpS.
    Apply invstepDTRc in SS2. SimpS.
    Apply step0_tcbv_C in H14. SimpS.
    Apply step_ibs in H; try apply pure_buildBus. SimpS.
    Apply step0_mb with H18 S3 in H19. SimpS.
    Apply step0_obs_sbf in H20. SimpS.
    assert (D1: Dtrs1 (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                      (globcir (false,false,false) cbs1 (ibs1 i2 i1) x43 (obs1 o2 o1)))
        by (constructor; try easy).
    Apply step_Dtrs1 with S3 SS3 in D1. SimpS.
    split. easy. split. easy.
    eapply sixsteps. 2: exact H19. 2: exact S4. 2: exact S5. 2: exact S6.
                     2: exact SS4. 2: exact SS5. 2: exact SS6. 2: exact SS7.
                     2:exact SS8. 2:exact SS9. CheckPure.
   (* no glitch *)
  - eapply step1_tcbv in H12; try (solve [constructor]). SimpS.
    Apply step_ibs in H; try apply pure_buildBus. SimpS.
    Purestep H13. Apply step1_mb with S2 D in H13. SimpS.
    Purestep H14. Apply step_obs_sf in H14. SimpS.
    assert (D1: Dtrs0 (ibs0 i1) (obs0 o1 o0) c1 c2
                      (globcir (b',b',b') cbs0 (ibs0 i1) x42 (obs0 o1 o0)))
                by (constructor; try easy).
    split. easy.
    eapply eightsteps. 2:exact D1. 2:exact S3. 2:exact S4. 2:exact S5. 2:exact S6.
                       2: exact SS2. 2:exact SS3. 2:exact SS4. 2:exact SS5.
                       2:exact SS6. 2:exact SS7. 2:exact SS8. 2:exact SS9. CheckPure.
Qed.


Lemma glitch_in_CB : forall S T (i0 i1 i2 i3 i4 i5: {|S|})
                           (o0 o1 o2 o3 o4 o5: {|T|})
                           (oo1 oo2 oo3 oo4 oo5 oo6 oo7 oo8 oo9:{|T # (T # T)|})
                           (c0 c1 c2 c3 c4 c5 c6: circuit S T)
                           (cc2' cc3 cc3' cc4 cc4' cc5 cc5' cc6: circuit S (T # (T # T)))
                            a a0 a1 b' b'0 b'1 c' cc,
                pure_bset {i0,i1,i2,i3,i4,i5,o0,o1,o2,o3,o4,o5}
             -> dtrs1 c0 c1 c2 cc
             -> bset2bool a b' -> bset2bool a0 b'0 -> bset2bool a1 b'1
             -> step c1 i1 o1 c2
             -> step c2 i2 o2 c3
             -> step c3 i3 o3 c4
             -> step c4 i4 o4 c5
             -> step c5 i5 o5 c6
             -> step (-{ b' }- (-{ b'0 }- (-{ b'1 }- c'))) i2 oo2 cc2'
             -> step  cc2' i2 oo3 cc3
             -> step  cc3  i3 oo4 cc3'
             -> step  cc3' i3 oo5 cc4
             -> step  cc4  i4 oo6 cc4'
             -> step  cc4' i4 oo7 cc5
             -> step  cc5  i5 oo8 cc5'
             -> step  cc5' i5 oo9 cc6
             -> PexInvDTR2 i1 {oo1, a, a0, a1} (bool2bset false)
                          (bool2bset false) (bool2bset false) (ibs1 i1 i0) cbs1 cc (obs1 o1 o0) c'
             -> atleast2 o0 oo1
             /\ atleast2 o1 oo3
             /\ atleast2 o2 oo5
             /\ atleast2 o3 oo7
             /\ atleast2 o4 oo9
             /\ Dtrs0 (ibs0 i5) (obs0 o5 o4) c5 c6 cc6.
Proof.
  introv P D B1 B2 B3.
  introv S2 S3 S4 S5 S6.
  introv SS2 SS3 SS4 SS5 SS6 SS7 SS8 SS9.
  introv H. unfold PexInvDTR2 in H. SimpS.
  apply stepg1_tcbv in H12. destruct H12 as [[X0 ?]|?]; SimpS.
  - apply invIG1 in X0. destruct X0 as [X0|[X0|[X0|[X0|[X0|X0]]]]]; SimpS.
      (* Standard reduction *)
    + Apply step_ibs in H; try apply pure_buildBus. SimpS.
      Purestep H13. Apply step1_mb with D S2 in H13. SimpS. Purestep H14.
      Apply step1_obs_sbf in H14; try apply pure_buildBus. SimpS.
      Apply invstepDTRc in SS2. SimpS.
      Apply step0_tcbv_C in H14. SimpS.
      Apply step_ibs in H; try apply pure_buildBus. SimpS.
      Apply step0_mb with H17 S3 in H18. SimpS.
      Apply step0_obs_sbf in H19. SimpS.
      assert (D1: Dtrs1 (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                       (globcir (false,false,false) cbs1 (ibs1 i2 i1) x43 (obs1 o2 o1)))
          by (constructor; try easy).
      Apply step_Dtrs1 with S3 SS3 in D1. SimpS.
      split. easy. split. easy.
      eapply sixsteps. 2: exact H18. 2: exact S4. 2: exact S5. 2: exact S6.
                       2: exact SS4. 2: exact SS5. 2: exact SS6. 2: exact SS7.
                       2:exact SS8. 2:exact SS9. CheckPure.
        (* Glitch on save wire *)
   + Apply step_ibs in H; try apply pure_buildBus. SimpS.
     Apply step1_mb_s with D S2 in H13. SimpS.
     Apply step_obs_sf in H14.
     assert (X: pure_bset (orS {bool2bset x21, bool2bset (negb (beq_buset_t o1 o0))}))
         by (Apply pure_orS).
     SimpS. Apply invstepDTRc in SS2. SimpS.
     Apply step0_tcbv_C in H13. SimpS.
     Apply step_ibs in H; try apply pure_buildBus. SimpS.
     Apply step0_mb_rr' with H12 S3 in H14. SimpS.
     Apply step0_obs_sbf in H15. SimpS.
     assert (D1: Dtr1_rr' (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                          (globcir (false,false,false) cbs1 (ibs1 i2 i1) x41 (obs1 o2 o1)))
        by (constructor; try easy).
     Apply step_Dtr1_rr' with SS3 in D1. SimpS.
     Apply step_Dtr0_r' with S4 SS4 in H14. SimpS.
     Apply step_Dtr1_r' with SS5 in H14. SimpS.
     split. easy. split. easy. split. easy.
     eapply foursteps. 2:exact H14. 2:exact S5. 2:exact S6.
                       2:exact SS6. 2:exact SS7. 2:exact SS8. 2:exact SS9. CheckPure.
   (* Glitch on rollBack wire *)
   + Apply step_ibs in H; try apply pure_buildBus. SimpS.
     Apply step1_mb_b with D S2 in H13. SimpS.
     Apply step1_obs_b in H14; try apply pure_buildBus. SimpS.
     Apply invstepDTRc in SS2. SimpS.
     Apply step0_tcbv_C in H15. SimpS.
     Apply step_ibs in H; try apply pure_buildBus. SimpS.
     Apply step0_mb_dr_F with H12 S3 in H16.
     destruct H16 as [H|H]; SimpS.
     (* make a lemma for d'rf *)
     * Apply step_obs_sf in H17. SimpS. rewrite rew_orS2 in H18. SimpS.
       assert (D1: Dtr1_d'rf (ibs1 i2 i1) (dtrOB_T o2 x25 o2 x26 o1) c1 c2 c3
                             (globcir (true,true,true) cbs1 (ibs1 i2 i1) x43
                                      (dtrOB_T o2 x25 o2 x26 o1)))
           by (constructor; try easy).
       Apply step_Dtr1_d'rf with S2 S3 SS3 in D1. SimpS.
       Apply step_Dtr2_d'rr' with S3 S4 SS4 in H16. SimpS.
       Apply step_Dtr3_d'rr' with S4 SS5 in H16. SimpS.
       Apply step_Dtr4_d'rr' with S5 SS6 in H16. SimpS.
       Apply step_Dtr5_d'rr' with S5 SS7 in H16. SimpS.
       Apply step_Dtr0_r' with S6 SS8 in H16. SimpS.
       Apply step_Dtr1_r' with SS9 in H16. SimpS.
       split; easy.
     * Apply step_obs_sf in H17. SimpS.
       case_eq (beq_buset_t x26 o1); intro E; rewrite E in H18; Inverts H18.
       { apply beq_buset_imp_eq in E. subst.
         assert (D1: Dtr1_r (ibs1 i2 i1) (dtrOB_T o2 x25 o2 o1 o1) c1 c2 c3
                             (globcir (false,false,false) cbs1 (ibs1 i2 i1) x43
                                      (dtrOB_T o2 x25 o2 o1 o1)))
             by (constructor; try easy).
         Apply step_Dtr1_r with SS3 in D1. SimpS.
         Apply step_Dtr0_r' with S4 SS4 in H16. SimpS.
         Apply step_Dtr1_r' with SS5 in H14. SimpS.
         split. easy. split. easy. split. easy.
         eapply foursteps. 2:exact H14. 2:exact S5. 2:exact S6.
                           2:exact SS6. 2:exact SS7. 2:exact SS8. 2:exact SS9. CheckPure. }
       { eapply dtr1_r_imp_d'r in H15.
         assert (D1: Dtr1_d'rf (ibs1 i2 i1) (dtrOB_T o2 x25 o2 x26 o1) c1 c2 c3
                                (globcir (true,true,true) cbs1 (ibs1 i2 i1) x43
                                         (dtrOB_T o2 x25 o2 x26 o1)))
            by (constructor; try easy).
         Apply step_Dtr1_d'rf  with S3 SS3 in D1. destruct D1 as [? D1]. SimpS.
         Apply step_Dtr2_d'rr' with S4 SS4 in D1. destruct D1 as [? D1]. SimpS.
         Apply step_Dtr3_d'rr' with S4 SS5 in D1. destruct D1 as [? D1]. SimpS.
         Apply step_Dtr4_d'rr' with S5 SS6 in D1. destruct D1 as [? D1]. SimpS.
         Apply step_Dtr5_d'rr' with S5 SS7 in D1. destruct D1 as [? D1]. SimpS.
         Apply step_Dtr0_r'    with S6 SS8 in D1. destruct D1 as [? D1]. SimpS.
         Apply step_Dtr1_r'    with SS9 in D1. SimpS.
         split; easy. }
      (* Glitch on fail wire *)
    + Apply step_ibs in H; try apply pure_buildBus. SimpS.
      Apply step1_mb_f with D S2 in H13. SimpS.
      Apply step_obs_sf in H14. SimpS.
      Apply invstepDTRc in SS2. SimpS.
      Apply step0_tcbv in H13. SimpS.
      Apply step_ibs in H; try apply pure_buildBus. SimpS.
      Apply step0_mb with H12 S3 in H14. SimpS.
      Apply step0_obs_sbf in H15. SimpS.
      assert (D1: Dtrs1 (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                       (globcir (false,false,false) cbs1 (ibs1 i2 i1) x41 (obs1 o2 o1)))
          by (constructor; try easy).
      Apply step_Dtrs1 with S3 SS3 in D1. SimpS.
      split. easy. split. easy.
      eapply sixsteps. 2: exact H14. 2: exact S4. 2: exact S5. 2: exact S6.
                       2: exact SS4. 2: exact SS5. 2: exact SS6. 2: exact SS7.
                       2:exact SS8. 2:exact SS9. CheckPure.
       (* Glitch on rB wire *)
    + Apply step_ib_rs in H; try apply pure_buildBus. SimpS.
      Apply step1_mb_i with D S2 in H13. SimpS.
      Apply step_obs_ibf in H14.
      assert (X: pure_bset (orS {bool2bset x25, bool2bset (negb (beq_buset_t o1 o0))}))
          by (Apply pure_orS). SimpS.
      eapply case0_dr in H12. 3: exact S2. 3: exact S3. 3: exact S4. 3: exact S5. 3: exact S6.
                              3: exact SS2. 3: exact SS3. 3: exact SS4. 3: exact SS5. 3: exact SS6.
                              3: exact SS7.  3: exact SS8. 3: exact SS9. 2: Checkpure.

      SimpS. split; easy.
       (* Glitch on subst wire *)
    + Apply step_ibs in H; try apply pure_buildBus. SimpS. Purestep H13.
      Apply step1_mb with D S2 in H13. SimpS.
      Apply step1_obs_u in H14. SimpS.
      assert (D1: Dtrs0 (ibs0 i1) (obs0 o1 o0) c1 c2
                       (globcir (b'1,b'1,b'1) cbs0 (ibs0 i1) x42 (obs0 o1 o0)))
          by (constructor; try easy).
       split. easy.
       eapply eightsteps. 2:exact D1. 2:exact S3. 2:exact S4. 2:exact S5. 2:exact S6.
                         2: exact SS2. 2:exact SS3. 2:exact SS4. 2:exact SS5.
                         2:exact SS6. 2:exact SS7. 2:exact SS8. 2:exact SS9. CheckPure.
   (* One copy of the triplicated contol block is corrupted *)
  - Apply step_ibs in H; try apply pure_buildBus. SimpS. Purestep H13.
    Apply step1_mb with D S2 in H13. SimpS. Purestep H14.
    Apply step1_obs_sbf in H14; try apply pure_buildBus. SimpS.
    Apply invstepDTRc in SS2. SimpS.
    Apply step0_tcbv_C in H14. SimpS.
    Apply step_ibs in H; try apply pure_buildBus. SimpS.
    Apply step0_mb with H18 S3 in H19. SimpS.
    Apply step0_obs_sbf in H20. SimpS.
    assert (D1: Dtrs1 (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                     (globcir (false,false,false) cbs1 (ibs1 i2 i1) x44 (obs1 o2 o1)))
        by (constructor; try easy).
    Apply step_Dtrs1 with S3 SS3 in D1. SimpS.
    split. easy. split. easy.
    eapply sixsteps. 2: exact H19. 2: exact S4. 2: exact S5. 2: exact S6.
                     2: exact SS4. 2: exact SS5. 2: exact SS6. 2: exact SS7.
                     2:exact SS8. 2:exact SS9. CheckPure.
Qed.

Lemma glitch_in_GC : forall S T (i0 i1 i2 i3 i4 i5: {|S|})
                           (o0 o1 o2 o3 o4 o5: {|T|})
                           (oo1 oo2 oo3 oo4 oo5 oo6 oo7 oo8 oo9:{|T # (T # T)|})
                           (c0 c1 c2 c3 c4 c5 c6: circuit S T)
                           (cc2' cc3 cc3' cc4 cc4' cc5 cc5' cc6: circuit S (T # (T # T)))
                            a a0 a1 b' b'0 b'1 c' cc,
                pure_bset {i0,i1,i2,i3,i4,i5,o0,o1,o2,o3,o4,o5}
             -> dtrs1 c0 c1 c2 cc
             -> bset2bool a b' -> bset2bool a0 b'0 -> bset2bool a1 b'1
             -> step c1 i1 o1 c2
             -> step c2 i2 o2 c3
             -> step c3 i3 o3 c4
             -> step c4 i4 o4 c5
             -> step c5 i5 o5 c6
             -> step (-{ b' }- (-{ b'0 }- (-{ b'1 }- c'))) i2 oo2 cc2'
             -> step  cc2' i2 oo3 cc3
             -> step  cc3  i3 oo4 cc3'
             -> step  cc3' i3 oo5 cc4
             -> step  cc4  i4 oo6 cc4'
             -> step  cc4' i4 oo7 cc5
             -> step  cc5  i5 oo8 cc5'
             -> step  cc5' i5 oo9 cc6
             -> stepg (dtrcore (ibs1 i1 i0) cbs1 cc (obs1 o1 o0))
                                {i1, bool2bset false, bool2bset false, bool2bset false}
                                {oo1, a, a0, a1} c'
             -> atleast2 o0 oo1
             /\ atleast2 o1 oo3
             /\ atleast2 o2 oo5
             /\ atleast2 o3 oo7
             /\ atleast2 o4 oo9
             /\ Dtrs0 (ibs0 i5) (obs0 o5 o4) c5 c6 cc6.
Proof.
  introv P D B1 B2 B3.
  introv S2 S3 S4 S5 S6.
  introv SS2 SS3 SS4 SS5 SS6 SS7 SS8 SS9.
  introv H. SimpS.
  Apply invstepgcore in H.
  destruct H as [H|[H|[H|H]]].
    (* Glitch occurring within the control block*)
  - eapply glitch_in_CB. 2: exact D. 2: exact B1. 2: exact B2. 2: exact B3.
                         2: exact S2. 2: exact S3. 2: exact S4. 2: exact S5. 2: exact S6.
                         2: exact SS2. 2: exact SS3. 2: exact SS4. 2: exact SS5.
                         2: exact SS6. 2: exact SS7. 2: exact SS8. 2: exact SS9.
                         2: exact H. CheckPure.
    (* Glitch occuring within the input buffers *)
  - unfold PexInvDTR3 in H. SimpS.
    Apply step1_tcbv in H12. SimpS.
    Apply stepg_ibs in H.
    destruct H as [?|?]; SimpS.
    (* output is corrupted but not the buffer *)
    * Apply step1_mb_i with D S in H13. SimpS.
      Apply step_obs_ibf in H14.
      assert (X: pure_bset (orS {bool2bset x25, bool2bset (negb (beq_buset_t o1 o0))}))
      by (Apply pure_orS). SimpS.
      eapply case0_dr in H12. 3: exact S2. 3: exact S3. 3: exact S4.
                              3: exact S5. 3: exact S6. 3: exact SS2.
                              3: exact SS3. 3: exact SS4. 3: exact SS5. 3: exact SS6.
                              3: exact SS7.  3: exact SS8. 3: exact SS9.  2: Checkpure.
      SimpS. split; easy.
   (* buffer is corrupted but not the output *)
    * Apply step1_mb with D S2 in H13. SimpS.
      Apply step1_obs_sbf in H14; try apply pure_buildBus. SimpS.
      Apply invstepDTRc in SS2.
      destruct SS2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?
                      [X[X4[X5[X6[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
      SimpS.
      Apply step0_tcbv in X4. SimpS.
      Apply step_ibs in X; try apply pure_buildBus. SimpS.
      Apply step0_mb with H13 S3 in X5. SimpS.
      Apply step0_obs_sbf in X6. SimpS.
      assert (D1: Dtrs1 (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                       (globcir (false,false,false) cbs1 (ibs1 i2 i1) x43 (obs1 o2 o1)))
          by (constructor; try easy).
      Apply step_Dtrs1 with S3 SS3 in D1.  SimpS.
      split. easy. split. easy.
      eapply sixsteps. 2: exact H14. 2: exact S4. 2: exact S5. 2: exact S6.
                       2: exact SS4. 2: exact SS5. 2: exact SS6. 2: exact SS7.
                       2:exact SS8.  2: exact SS9. CheckPure.
(* Glitch occuring withinin the main transformed circuit *)
  - unfold PexInvDTR4 in H. SimpS.
    apply step1_tcbv in H12. SimpS.
    Apply step_ibs in H; try apply pure_buildBus. SimpS.
    Apply stepg1_mb with D S2 in H13.
    destruct H13 as [H|[H|[H|H]]]; SimpS.
    (* r-cells are corrupted *)
    * Purestep H14. Apply step1_obs_sbf in H14. SimpS.
      assert (D1: Dtr0_r (ibs0 i1) (obs0 o1 o0) c1 c2
                       (globcir (b',b',b') cbs0 (ibs0 i1) x42 (obs0 o1 o0)))
          by (constructor; try easy).
      Apply step_Dtr0_r  with S3 SS2 in D1. SimpS.
      Apply step_Dtr1_r  with SS3 in H14. SimpS.
      Apply step_Dtr0_r' with S4 SS4 in H14. SimpS.
      Apply step_Dtr1_r' with S4 SS5 in H14. SimpS.
      split. easy. split. easy. split. easy.
      eapply foursteps. 2:exact H14. 2:exact S5. 2:exact S6.
                        2:exact SS6. 2:exact SS7. 2:exact SS8. 2:exact SS9. CheckPure.
    (* r'-cells are corrupted *)
    * Purestep H14. Apply step1_obs_sbf in H14. SimpS.
      assert (D1: Dtr0_r' (ibs0 i1) (obs0 o1 o0) c1 c2
                       (globcir (b',b',b') cbs0 (ibs0 i1) x42 (obs0 o1 o0)))
          by (constructor; try easy).
      Apply step_Dtr0_r'  with S3 SS2 in D1. SimpS.
      Apply step_Dtr1_r' with SS3 in H14. SimpS.
      split. easy. split. easy.
      eapply sixsteps. 2: exact H14. 2: exact S4. 2: exact S5. 2: exact S6.
                       2: exact SS4. 2: exact SS5. 2: exact SS6. 2: exact SS7.
                       2:exact SS8. 2:exact SS9. CheckPure.
    (* d and r -cells are corrupted *)
    * Apply step_obs_ibf in H14. SimpS.
      split. easy. eapply case0_dr in H12. 3: exact S2. 3: exact S3. 3: exact S4.
                                            3: exact S5. 3: exact S6. 3: exact SS2.
                                            3: exact SS3. 3: exact SS4. 3: exact SS5. 3: exact SS6.
                                            3: exact SS7.  3: exact SS8. 3: exact SS9.  2: Checkpure.
      SimpS. split; easy.
   (* d'-cells corrupted *)
    * Apply step1_obs_sbf in H14. SimpS.
      split. easy.
      Apply invstepDTRc in SS2. SimpS.
      Apply step0_tcbv in H13. SimpS.
      Apply step_ibs in H; try apply pure_buildBus. SimpS.
      Apply step0_mb_d' with H12 S3 in H14.
      destruct H14; SimpS.
      { Apply step0_obs_sbf in H15. SimpS.
        assert (D1: Dtrs1 (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                         (globcir (false,false,false) cbs1 (ibs1 i2 i1) x41 (obs1 o2 o1)))
            by (constructor; try easy).
        Apply step_Dtrs1 with S3 SS3 in D1. SimpS.
        split. easy.
        eapply sixsteps. 2:exact H14. 2:exact S4. 2:exact S5. 2:exact S6.
                         2:exact SS4. 2:exact SS5. 2:exact SS6. 2:exact SS7.
                         2:exact SS8. 2:exact SS9. CheckPure.  }
      { Apply step_obs_sf in H15. rewrite rew_orS2 in H15. SimpS.
        assert (D1: Dtr1_df (ibs1 i2 i1) (dtrOB_T x18 o1 x18 o1 o1) c1 c2 c3
                            (globcir (true,true,true) cbs1 (ibs1 i2 i1) x41 (dtrOB_T x18 o1 x18 o1 o1)))
            by (constructor; try easy).
        Apply step_Dtr1_df     with S3 SS3 in D1. SimpS.
        Apply step_Dtr2_d'rr'' with S3 S4 SS4 in H15. SimpS.
        Apply step_Dtr3_d'rr'' with S4 SS5 in H15. SimpS.
        Apply step_Dtr4_d'rr'  with S5 SS6 in H15. SimpS.
        Apply step_Dtr5_d'rr'  with S5 SS7 in H15. SimpS.
        Apply step_Dtr0_r'     with S6 SS8 in H15. SimpS.
        Apply step_Dtr1_r'     with S6 SS9 in H15. SimpS.
        split; easy. }
   (* Glitch occuring within the output buffers *)
  - unfold PexInvDTR5 in H. SimpS.
    apply step1_tcbv in H12. SimpS.
    Apply step_ibs in H; try apply pure_buildBus. SimpS. Purestep H13.
    Apply step1_mb with D S2 in H13. SimpS.
    (* Purestep H1. SimpS. *)
    Apply stepg1_obs in H14. SimpS.
    destruct H14 as [?|[?|?]]; SimpS.
    * Apply invstepDTRc in SS2. SimpS.
      Apply step0_tcbv in H18. SimpS.
      Apply step_ibs in H14; try apply pure_buildBus. SimpS.
      Apply step0_mb with H17 S3 in H19. SimpS.
      replace {~0, ~0, ~0, ~0} with {~0, ~0, bool2bset false, ~0} in H20. 2: easy.
      Apply step_obs_sf in H20. rewrite beq_buset_reflx in H20. cbn in H20. SimpS.
      assert (D1: Dtrs1 (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                       (globcir (false,false,false) cbs1 (ibs1 i2 i1) x48 (obs1 o2 o1)))
          by (constructor; try easy).
      Apply step_Dtrs1 with SS3 in D1. SimpS.
      eapply sixsteps in H19. 3: exact S4. 3: exact S5. 3: exact S6.
                              3: exact SS4. 3: exact SS5. 3: exact SS6. 3: exact SS7.
                              3: exact SS8. 3: exact SS9. 2: CheckPure.
      destruct H as [H|[H|H]]; SimpS; split; easy.
    * Apply invstepDTRc in SS2. SimpS.
      Apply step0_tcbv in H18. SimpS.
      Apply step_ibs in H14; try apply pure_buildBus. SimpS.
      Apply step0_mb with H17 S3 in H19. SimpS.
      Apply step_obs_sf in H20. SimpS.
      case_eq (x40); introv C; subst.
      (* Error detected *)
      { Apply invstepDTRc in SS3. SimpS.
        Apply stepr1_tcbv in H19. SimpS.
        Apply step12_ibs in H14; try apply pure_buildBus. SimpS.
        apply dtrs1_imp_dtr1_d'r in H18.
        Apply step1_mb_d'r with H18 S2 in H20. SimpS.
        Apply stepr1_obs in H22. SimpS.
        apply dtrec_rr'_imp_d'rr' in H19.
        assert (D1: Dtr2_d'rr' (ibs0 i2) (dtrOB_T o1 o2 o1 o2 o1) c3 c2
                                (globcir (x33,x33,x33) cbs2 (ibs0 i2) x45 (dtrOB_T o1 o2 o1 o2 o1)))
            by (constructor; try easy).
        Apply step_Dtr2_d'rr' with S3 S4 SS4 in D1. SimpS.
        Apply step_Dtr3_d'rr' with S4 SS5 in H20. SimpS.
        Apply step_Dtr4_d'rr' with S5 SS6 in H20. SimpS.
        Apply step_Dtr5_d'rr' with S5 SS7 in H20. SimpS.
        Apply step_Dtr0_r'    with S6 SS8 in H20. SimpS.
        Apply step_Dtr1_r'    with S6 SS9 in H20. SimpS.
        destruct H as [H|[H|H]]; SimpS; split; easy. }
        (* No error detected *)
      { Apply invstepDTRc in SS3. SimpS.
        Apply step1_tcbv in H19. SimpS.
        Apply step_ibs in H14; try apply pure_buildBus. SimpS.
        Apply step1_mb with H18 S3 in H20. SimpS.
        Apply step_obs_sf in H22. SimpS.
        assert (D1: Dtrs0 (ibs0 i2) (obs0 o2 o1) c2 c3
                                (globcir (x33,x33,x33) cbs0 (ibs0 i2) x45 (obs0 o2 o1)))
            by (constructor; try easy).
        Apply step_Dtrs0 with S4 SS4 in D1. SimpS.
        Apply step_Dtrs1 with S4 SS5 in H20. SimpS.
        eapply foursteps in H20.  3:exact S5. 3:exact S6. 3:exact SS6.
                                  3:exact SS7. 3:exact SS8. 3:exact SS9. 2:CheckPure.
        destruct H as [H|[H|H]]; SimpS; split; easy. }
    * Apply invstepDTRc in SS2. SimpS.
      Apply step0_tcbv in H18. SimpS.
      Apply step_ibs in H14; try apply pure_buildBus. SimpS.
      Apply step0_mb with H17 S3 in H19. SimpS.
      Apply step0_obs_sbf in H20. SimpS.
      assert (D1: Dtrs1 (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                       (globcir (false,false,false) cbs1 (ibs1 i2 i1) x48 (obs1 o2 o1)))
          by (constructor; try easy).
      Apply step_Dtrs1 with S3 SS3 in D1. SimpS.
      eapply sixsteps in H19. 3: exact S4. 3: exact S5. 3: exact S6.
                              3: exact SS4. 3: exact SS5. 3: exact SS6. 3: exact SS7.
                              3: exact SS8. 3: exact SS9. 2: CheckPure.
      destruct H as [H|[H|H]]; SimpS; split; easy.
Qed.