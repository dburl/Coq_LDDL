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

Lemma glitch0_in_3fail : forall S T (i0 i1 i2 i3 i4 i5: {|S|})
                           (o o0 o1 o2 o3 o4 o5: {|T|})
                           (oo0 oo1 oo2 oo3 oo4 oo5 oo6 oo7 oo8 oo9:{|T # (T # T)|})
                           (c0 c1 c2 c3 c4 c5 c6: circuit S T)
                           (cc2 cc2' cc3 cc3' cc4 cc4' cc5 cc5' cc6: circuit S (T # (T # T)))
                            a a0 a1 b' b'0 b'1 f bg c' cc,
                pure_bset {i0,i1,i2,i3,i4,i5,o,o0,o1,o2,o3,o4,o5}
             -> dtrs0 c0 c1 cc
             -> bset2bool a b' -> bset2bool a0 b'0 -> bset2bool a1 b'1
             -> introglitch (bool2bset f) bg
             -> step c1 i1 o1 c2
             -> step c2 i2 o2 c3
             -> step c3 i3 o3 c4
             -> step c4 i4 o4 c5
             -> step c5 i5 o5 c6
             -> step (-{ b' }- (-{ b'0 }- (-{ b'1 }- c'))) i1 oo1 cc2
             -> step  cc2  i2 oo2 cc2'
             -> step  cc2' i2 oo3 cc3
             -> step  cc3  i3 oo4 cc3'
             -> step  cc3' i3 oo5 cc4
             -> step  cc4  i4 oo6 cc4'
             -> step  cc4' i4 oo7 cc5
             -> step  cc5  i5 oo8 cc5'
             -> step  cc5' i5 oo9 cc6
             -> step (dtrcore (ibs0 i0) cbs0 cc (obs0 o0 o)) {i1, bool2bset f, bool2bset f, bg}
                                                              {oo0, a, a0, a1} c'
             -> atleast2 o0 oo1
             /\ atleast2 o1 oo3
             /\ atleast2 o2 oo5
             /\ atleast2 o3 oo7
             /\ atleast2 o4 oo9
             /\ Dtrs0 (ibs0 i5) (obs0 o5 o4) c5 c6 cc6.
Proof.
  introv P D B1 B2 B3 I.
  introv S2 S3 S4 S5 S6.
  introv SS2 SS3 SS4 SS5 SS6 SS7 SS8 SS9 SS10.
  introv H. SimpS.
  eapply invstepcore in H; try easy.
  unfold PexInvDTR1 in H. SimpS.
  eapply step0_tcbv_i with (fI:=bool2bset f) in H13; try CheckPure. SimpS.
  apply step_ibs in H; try apply pure_buildBus; try easy. SimpS.
  eapply step0_mb in H14; try exact D; try exact S2; try easy. SimpS.
  Purestep H15. SimpS.
  eapply step0_obs_sfu in H15; try easy. SimpS.
  apply invstepDTRc in SS2; try CheckPure. SimpS.
  eapply step1_tcbv_C in H15; try exact H16; try CheckPure. SimpS.
  apply step_ibs in H; try apply pure_buildBus; try easy. SimpS.
  eapply step1_mb in H17;  try exact H13; try exact S2; try easy. SimpS.
  Apply step_obs_sf in H18. SimpS.
  assert (D1: Dtrs0 (ibs0 i1) (obs0 o1 o0) c1 c2
                   (globcir (x37,x37,x37) cbs0 (ibs0 i1) x44 (obs0 o1 o0)))
      by (constructor; try easy).
  split. easy.
  eapply eightsteps. 2: exact D1. 2: exact S3. 2: exact S4. 2: exact S5. 2: exact S6.
                     2: exact SS3. 2: exact SS4. 2: exact SS5. 2: exact SS6. 2: exact SS7.
                     2:exact SS8. 2:exact SS9. 2:exact SS10. CheckPure.
Qed.

Lemma glitch0_in_CB : forall S T (i0 i1 i2 i3 i4 i5: {|S|})
                           (o o0 o1 o2 o3 o4 o5: {|T|})
                           (oo0 oo1 oo2 oo3 oo4 oo5 oo6 oo7 oo8 oo9:{|T # (T # T)|})
                           (c0 c1 c2 c3 c4 c5 c6: circuit S T)
                           (cc2 cc2' cc3 cc3' cc4 cc4' cc5 cc5' cc6: circuit S (T # (T # T)))
                            a a0 a1 b' b'0 b'1 f c' cc,
                pure_bset {i0,i1,i2,i3,i4,i5,o,o0,o1,o2,o3,o4,o5}
             -> dtrs0 c0 c1 cc
             -> bset2bool a b' -> bset2bool a0 b'0 -> bset2bool a1 b'1
             (*-> introglitch (bool2bset false) bg*)
             -> step c0 i0 o0 c1
             -> step c1 i1 o1 c2
             -> step c2 i2 o2 c3
             -> step c3 i3 o3 c4
             -> step c4 i4 o4 c5
             -> step c5 i5 o5 c6
             -> step (-{ b' }- (-{ b'0 }- (-{ b'1 }- c'))) i1 oo1 cc2
             -> step  cc2  i2 oo2 cc2'
             -> step  cc2' i2 oo3 cc3
             -> step  cc3  i3 oo4 cc3'
             -> step  cc3' i3 oo5 cc4
             -> step  cc4  i4 oo6 cc4'
             -> step  cc4' i4 oo7 cc5
             -> step  cc5  i5 oo8 cc5'
             -> step  cc5' i5 oo9 cc6
             -> PexInvDTR2 i1 {oo0, a, a0, a1} (bool2bset f) (bool2bset f) (bool2bset f)
                                              (ibs0 i0) cbs0 cc (obs0 o0 o) c'
             -> atleast2 o0 oo1
             /\ atleast2 o1 oo3
             /\ atleast2 o2 oo5
             /\ atleast2 o3 oo7
             /\ atleast2 o4 oo9
             /\ Dtrs0 (ibs0 i5) (obs0 o5 o4) c5 c6 cc6.
Proof.
  introv P D B1 B2 B3.
  introv S1 S2 S3 S4 S5 S6.
  introv SS2 SS3 SS4 SS5 SS6 SS7 SS8 SS9 SS10.
  introv H. unfold PexInvDTR2 in H. SimpS.
  apply stepg0_tcbv in H13; try CheckPure.
  destruct H13 as [X0|X0]; SimpS.
  - apply invIG1 in H13. destruct H13 as [X0|[X0|[X0|[X0|[X0|X0]]]]]; SimpS.
      (* Standard reduction *)
    + apply step_ibs in H; try apply pure_buildBus; try easy. SimpS.
      Purestep H14. eapply step0_mb in D; try exact H14; try exact S2; try CheckPure.
      SimpS. Purestep H15.
      eapply step0_obs_sbf in H15; try apply pure_buildBus; try easy.
      SimpS.
      apply invstepDTRc in SS2; try CheckPure. SimpS.
      replace {bool2bset false, bool2bset false, bool2bset false} with {~0,~0,~0} in H13. 2: easy.
      eapply step1_tcbv in H13; try exact H6; try CheckPure. SimpS.
      apply step_ibs in H; try apply pure_buildBus; try easy. SimpS.
      eapply step1_mb in H15; try exact H19; try exact S2; try easy. SimpS.
      eapply step1_obs_sbf in H17; try easy. SimpS.
      assert (D: Dtrs0 (ibs0 i1) (obs0 o1 o0) c1 c2
                       (globcir (x36,x36,x36) cbs0 (ibs0 i1) x43 (obs0 o1 o0)))
          by (constructor; try easy).
      split. easy.
      eapply eightsteps. 2: exact D. 2: exact S3. 2: exact S4. 2: exact S5. 2: exact S6.
                         2: exact SS3. 2: exact SS4. 2: exact SS5. 2: exact SS6. 2: exact SS7.
                         2:exact SS8. 2:exact SS9. 2: exact SS10. CheckPure.
        (* Glitch on save wire *)
   + apply step_ibs in H; try apply pure_buildBus; try easy. SimpS.
     eapply step0_mb_s in D; try exact H14; try exact S2; try CheckPure.
     SimpS.
     eapply step0_obs_sbf in H15; try CheckPure. SimpS.
     apply invstepDTRc in SS2; try CheckPure. SimpS.
     eapply step1_tcbv in H15; try exact H6; try CheckPure. SimpS.
     apply step_ibs in H; try apply pure_buildBus; try easy. SimpS.
     eapply step1_mb_rr' in H16;  try exact H13; try exact S2; try easy. SimpS.
     eapply step1_obs_sbf in H17; try easy. SimpS.
     assert (D: Dtr0_r' (ibs0 i1) (obs0 o1 o0) c1 c2
                          (globcir (x36,x36,x36) cbs0 (ibs0 i1) x43 (obs0 o1 o0)))
        by (constructor; try easy).
     eapply step_Dtr0_r' in D; try exact S3; try exact SS3; try easy. SimpS.
     eapply step_Dtr1_r' in H16; try exact SS4; try easy. SimpS.
     split. easy. split. easy.
     eapply sixsteps. 2:exact H16. 2: exact S4. 2:exact S5. 2:exact S6.
                      2:exact SS5. 2: exact SS6. 2:exact SS7. 2:exact SS8.
                      2:exact SS9. 2: exact SS10. CheckPure.
   (* Glitch on rollBack wire *)
   + apply step_ibs in H; try apply pure_buildBus; try easy. SimpS.
     eapply step0_mb_b in D; try exact H14; try exact S2; try CheckPure. SimpS.
     eapply step0_obs_b in H15; try apply pure_buildBus; try easy. SimpS.
     assert (D: Dtr1_d (ibs1 i1 i0) (dtrOB_T x27 o0 x28 o0 o0) c0 c1 c2
                          (globcir (false,false,false) cbs1 (ibs1 i1 i0) x45 (dtrOB_T x27 o0 x28 o0 o0)))
        by (constructor; try easy).
     eapply step_Dtr1_d in D; try exact S2; try exact SS2; try CheckPure. SimpS.
     eapply step_Dtr0_d' in H17; try exact S3; try exact SS3; try CheckPure.
     destruct H17 as [G|[z [? G]]].
     * eapply step_Dtr1 in G; try exact S3; try exact SS4; try CheckPure. SimpS.
       split. easy.  split. easy.
       eapply sixsteps. 2: exact H17. 2: exact S4. 2: exact S5. 2: exact S6.
                        2: exact SS5. 2: exact SS6. 2: exact SS7.
                        2:exact SS8. 2:exact SS9. 2: exact SS10. CheckPure.
     * split. easy.
       eapply case1_df. 2: exact G. 2:exact S2. 2: exact S3.
                        2:exact S4. 2:exact S5. 2:exact S6.
                        2:exact SS4. 2:exact SS5. 2:exact SS6.
                        2:exact SS7. 2:exact SS8. 2:exact SS9.
                        2:exact SS10. CheckPure.
      (* Glitch on fail wire *)
    + apply step_ibs in H; try apply pure_buildBus; try easy. SimpS.
      eapply step0_mb_f in D; try exact H14; try exact S2; try CheckPure. SimpS.
      Apply step_obs_sf in H15. SimpS.
      Apply invstepDTRc in SS2. SimpS.
      assert (X: corrupt_1in3_bus (~0) {bool2bset b', bool2bset b'0, bool2bset b'1}
              \/ corrupt_1in3_bus (~1) {bool2bset b', bool2bset b'0, bool2bset b'1})
          by (destruct b'; destruct b'0; destruct b'1;
              try (right; constructor); try (left; constructor)).
      destruct X as [X|X].
      * Apply step1_tcbv_i in H15. SimpS.
        apply step_ibs in H; try apply pure_buildBus; try easy. SimpS.
        eapply step1_mb in H16; try exact H13; try exact S2; try easy. SimpS.
        Apply step_obs_sf in H17. SimpS.
        Apply invstepDTRc in SS3. SimpS.
        eapply step0_tcbv_C in H16; try exact H33; try CheckPure. SimpS.
        apply step_ibs in H; try apply pure_buildBus; try easy. SimpS.
        eapply step0_mb in H17; try exact H15; try exact S3; try easy. SimpS.
        eapply step0_obs_sbf in H19; try easy. SimpS.
        assert (D: Dtrs1 (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                       (globcir (false,false,false) cbs1 (ibs1 i2 i1) x44 (obs1 o2 o1)))
          by (constructor; try easy).
        split. easy.
        eapply step_Dtrs1 in D; try exact S3; try exact SS4; try easy. SimpS.
        split. easy.
        eapply sixsteps. 2: exact H17. 2: exact S4. 2: exact S5. 2: exact S6.
                         2: exact SS5. 2: exact SS6. 2: exact SS7.
                         2:exact SS8. 2:exact SS9. 2: exact SS10. CheckPure.
      * eapply stepr1_tcbv_i in H15; try CheckPure. SimpS.
        apply step12_ibs in H; try apply pure_buildBus; try easy. SimpS.
        eapply dtrs1_imp_dtr1_d'r in H13.
        eapply step1_mb_d'r in H16; try exact H13; try exact S1; try easy. SimpS.
        eapply stepr1_obs in H17; try easy. SimpS.
        apply invstepDTRc in SS3; try CheckPure. SimpS.
        eapply stepr2_tcbv_C in H16; try exact H33; try CheckPure. SimpS.
        eapply step12_ibs in H; try apply pure_buildBus; try easy. SimpS.
        eapply dtrec_rr'_imp_d'rr' in H15.
        eapply stepr2_mb_d'rr' in H17; try exact S2; try easy. SimpS.
        eapply stepr23_obs in H19; try easy. SimpS.
        assert (D: Dtr3_d'rr' (ibs1 i2 i1) (dtrOB_T o1 o0 o1 o0 o1) c1 c2
                               (globcir (x35,x35,x35) cbs3 (ibs1 i2 i1) x44 (dtrOB_T o1 o0 o1 o0 o1)))
            by (constructor; try easy).
        split. easy.
        eapply case3_d'rr'. 2:exact D.  2:exact S2. 2: exact S3. 2: exact S4.
                            2:exact S5. 2:exact S6. 2:exact SS4. 2:exact SS5.
                            2: exact SS6. 2:exact SS7. 2:exact SS8.
                            2:exact SS9. 2: exact SS10. CheckPure.
       (* Glitch on rB wire *)
    + apply step_ib_rs in H; try apply pure_buildBus; try easy. subst.
      eapply step0_mb_i in D; try exact H14; try exact S2; try CheckPure. SimpS.
      eapply step_obs_ibf in H15; try CheckPure.
      rewrite beq_buset_reflx in H15. cbn in H15. SimpS.
      assert (D: Dtr1_d (ibs1 i1 i0) (dtrOB_T x28 o0 x29 o0 o0) c0 c1 c2
                           (globcir (false,false,false) cbs1 (ibs1 i1 i0) x45 (dtrOB_T x28 o0 x29 o0 o0)))
         by (constructor; try easy).
      eapply step_Dtr1_d in D; try exact S2; try exact SS2; try CheckPure. SimpS.
      eapply step_Dtr0_d' in H17; try exact S3; try exact SS3; try CheckPure.
      destruct H17 as [X|[z [? X]]]; SimpS.
      * eapply step_Dtr1 in X; try exact S3; try exact SS4; try CheckPure. SimpS.
        split. easy. split. easy.
        eapply sixsteps. 2:exact H17. 2: exact S4. 2:exact S5. 2:exact S6.
                         2:exact SS5. 2: exact SS6. 2:exact SS7. 2:exact SS8.
                         2:exact SS9. 2: exact SS10. CheckPure.
      * split. easy.
        eapply case1_df. 2: exact X. 2:exact S2. 2: exact S3.
                         2:exact S4. 2:exact S5. 2:exact S6.
                         2:exact SS4. 2:exact SS5. 2:exact SS6.
                         2:exact SS7. 2:exact SS8. 2:exact SS9.
                         2:exact SS10. CheckPure.
       (* Glitch on subst wire *)
    + apply step_ibs in H; try apply pure_buildBus; try easy. SimpS.
      eapply step0_mb in D; try exact H14; try exact S2; try CheckPure. SimpS.
      replace {~ 0, ~ 0, ~ 0, ~ ?} with {~ 0, ~ 0, bool2bset false, ~ ?} in H15. 2: easy.
      eapply step0_obs_u in H15; try CheckPure. SimpS.
      assert (D: Dtrs1 (ibs1 i1 i0) (obs1 o1 o0) c0 c1 c2
                       (globcir (false,false,false) cbs1 (ibs1 i1 i0) x45 (obs1 o1 o0)))
        by (constructor; try easy).
      eapply step_Dtrs1 in D; try exact S2; try exact SS2; try easy. SimpS.
      split. easy.
      eapply eightsteps. 2:exact H15. 2:exact S3. 2:exact S4. 2:exact S5. 2:exact S6.
                         2:exact SS3. 2:exact SS4. 2:exact SS5. 2:exact SS6.
                         2:exact SS7. 2:exact SS8. 2:exact SS9. 2:exact SS10. CheckPure.
   (* One copy of the triplicated contol block is corrupted *)
  - apply step_ibs in H; try apply pure_buildBus; try easy. SimpS.
    Purestep H14. eapply step0_mb in D; try exact H14; try exact S2; try CheckPure.
    SimpS. Purestep H15.
    eapply step0_obs_sbf in H15; try apply pure_buildBus; try easy.
    SimpS.
    apply invstepDTRc in SS2; try CheckPure. SimpS.
    eapply step1_tcbv_C in H13; try exact H16; try CheckPure. SimpS.
    apply step_ibs in H; try apply pure_buildBus; try easy. SimpS.
    eapply step1_mb in H15;  try exact H20; try exact S2; try easy. SimpS.
    eapply step_obs_sf in H18; try CheckPure. SimpS.
    assert (D: Dtrs0 (ibs0 i1) (obs0 o1 o0) c1 c2
                     (globcir (x37,x37,x37) cbs0 (ibs0 i1) x44 (obs0 o1 o0)))
          by (constructor; try easy).
    split. easy.
    eapply eightsteps. 2: exact D. 2: exact S3. 2: exact S4. 2: exact S5. 2: exact S6.
                       2: exact SS3. 2: exact SS4. 2: exact SS5. 2: exact SS6. 2: exact SS7.
                       2:exact SS8. 2:exact SS9. 2: exact SS10. CheckPure.
Qed.


Lemma glitch0_in_GC : forall S T (i0 i1 i2 i3 i4 i5: {|S|})
                           (o o0 o1 o2 o3 o4 o5: {|T|})
                           (oo0 oo1 oo2 oo3 oo4 oo5 oo6 oo7 oo8 oo9:{|T # (T # T)|})
                           (c0 c1 c2 c3 c4 c5 c6: circuit S T)
                           (cc2 cc2' cc3 cc3' cc4 cc4' cc5 cc5' cc6: circuit S (T # (T # T)))
                            a a0 a1 b' b'0 b'1 f c' cc,
                pure_bset {i0,i1,i2,i3,i4,i5,o,o0,o1,o2,o3,o4,o5}
             -> dtrs0 c0 c1 cc
             -> bset2bool a b' -> bset2bool a0 b'0 -> bset2bool a1 b'1
             -> step c0 i0 o0 c1
             -> step c1 i1 o1 c2
             -> step c2 i2 o2 c3
             -> step c3 i3 o3 c4
             -> step c4 i4 o4 c5
             -> step c5 i5 o5 c6
             -> step (-{ b' }- (-{ b'0 }- (-{ b'1 }- c'))) i1 oo1 cc2
             -> step  cc2  i2 oo2 cc2'
             -> step  cc2' i2 oo3 cc3
             -> step  cc3  i3 oo4 cc3'
             -> step  cc3' i3 oo5 cc4
             -> step  cc4  i4 oo6 cc4'
             -> step  cc4' i4 oo7 cc5
             -> step  cc5  i5 oo8 cc5'
             -> step  cc5' i5 oo9 cc6
             -> stepg (dtrcore (ibs0 i0) cbs0 cc (obs0 o0 o))
                                {i1, bool2bset f, bool2bset f, bool2bset f}
                                {oo0, a, a0, a1} c'
             -> atleast2 o0 oo1
             /\ atleast2 o1 oo3
             /\ atleast2 o2 oo5
             /\ atleast2 o3 oo7
             /\ atleast2 o4 oo9
             /\ Dtrs0 (ibs0 i5) (obs0 o5 o4) c5 c6 cc6.
Proof.
  introv P D B1 B2 B3.
  introv S1 S2 S3 S4 S5 S6.
  introv SS2 SS3 SS4 SS5 SS6 SS7 SS8 SS9 SS10.
  introv H. SimpS.
  eapply invstepgcore in H; try easy.
  destruct H as [H|[H|[H|H]]].
   (* Glitch occurring within the control block*)
  - eapply glitch0_in_CB. 2: exact D. 2: exact B1. 2: exact B2. 2: exact B3.
                          2: exact S1. 2: exact S2. 2: exact S3. 2: exact S4. 2: exact S5.
                          2: exact S6. 2: exact SS2. 2: exact SS3. 2: exact SS4.
                          2: exact SS5. 2: exact SS6. 2: exact SS7. 2: exact SS8.
                          2: exact SS9. 2: exact SS10. 2: exact H. CheckPure.
    (* Glitch occuring within the input buffers *)
  - unfold PexInvDTR3 in H. SimpS.
    eapply step0_tcbv in H13; try CheckPure. SimpS.
    eapply stepg_ibs in H; try easy.
    destruct H as [?|?]; SimpS.
    (* output is corrupted but not the buffer *)
    + eapply step0_mb_i in D; try exact S2; try exact H14; try easy. SimpS.
      eapply step_obs_ibf in H15; try CheckPure.
      rewrite beq_buset_reflx in H15. cbn in H15. SimpS.
      assert (D: Dtr1_d (ibs1 i1 i0) (dtrOB_T x28 o0 x29 o0 o0) c0 c1 c2
                         (globcir (false,false,false) cbs1 (ibs1 i1 i0) x45 (dtrOB_T x28 o0 x29 o0 o0)))
         by (constructor; try easy).
      eapply step_Dtr1_d in D; try exact S2; try exact SS2; try CheckPure. SimpS.
      eapply step_Dtr0_d' in H17; try exact S3; try exact SS3; try CheckPure. SimpS.
      destruct H17 as [X | [z [? X]]].
      * eapply step_Dtr1 in X; try exact S3; try exact SS4; try CheckPure. SimpS.
        split. easy. split. easy.
        eapply sixsteps. 2: exact H17. 2: exact S4. 2: exact S5. 2: exact S6.
                         2: exact SS5. 2: exact SS6. 2: exact SS7.
                         2:exact SS8. 2:exact SS9. 2: exact SS10. CheckPure.
      * split. easy.
        eapply case1_df. 2: exact X. 2:exact S2. 2: exact S3.
                         2:exact S4. 2:exact S5. 2:exact S6.
                         2:exact SS4. 2:exact SS5. 2:exact SS6.
                         2:exact SS7. 2:exact SS8. 2:exact SS9.
                         2:exact SS10. CheckPure.
   (* buffer is corrupted but not the output *)
    + eapply step0_mb in D; try exact H14; try exact S2; try CheckPure.
      SimpS.
      eapply step0_obs_sbf in H15; try apply pure_buildBus; try easy.
      SimpS.
      eapply invstepDTRc in SS2; try CheckPure.
      destruct SS2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?
                      [X[X4[X5[X6[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
      SimpS.
      apply step1_tcbv in X4; try CheckPure. SimpS.
      apply step_ibs in X; try apply pure_buildBus; try easy. SimpS.
      eapply step1_mb in X5; try exact H16; try exact S2; try CheckPure. SimpS.
      eapply step1_obs_sbf in X6; try easy. SimpS.
      assert (D: Dtrs0 (ibs0 i1) (obs0 o1 o0) c1 c2
                       (globcir (x37,x37,x37) cbs0 (ibs0 i1) x44 (obs0 o1 o0)))
          by (constructor; try easy). split. easy.
      eapply eightsteps. 2:exact D. 2:exact S3. 2:exact S4. 2:exact S5. 2:exact S6.
                         2: exact SS3. 2:exact SS4. 2:exact SS5. 2:exact SS6. 2:exact SS7.
                         2:exact SS8. 2:exact SS9. 2: exact SS10. CheckPure.
(* Glitch occuring withinin the main transformed circuit *)
  - unfold PexInvDTR4 in H. SimpS.
    eapply step0_tcbv in H13; try CheckPure. SimpS.
    apply step_ibs in H; try apply pure_buildBus; try easy. SimpS.
    eapply stepg0_mb in D; try exact S2; try exact H14; try easy.
    destruct D as [H|[H|[H|H]]]; SimpS.
    (* r-cells are corrupted *)
    + eapply step0_obs_sbf in H15; try easy. SimpS.
      assert (D: Dtr1_r (ibs1 i1 i0) (obs1 o1 o0) c0 c1 c2
                       (globcir (false,false,false) cbs1 (ibs1 i1 i0) x45 (obs1 o1 o0)))
          by (constructor; try easy).
      eapply step_Dtr1_r in D; try exact S3; try exact SS2; try easy. SimpS.
      eapply step_Dtr0_r' in H15; try exact S3; try exact SS3; try easy. SimpS.
      eapply step_Dtr1_r' in H15; try exact S4; try exact SS4; try easy. SimpS.
      split. easy. split. easy.
      eapply sixsteps. 2: exact H15. 2: exact S4. 2: exact S5. 2: exact S6.
                       2: exact SS5. 2: exact SS6. 2: exact SS7. 2:exact SS8.
                       2:exact SS9. 2:exact SS10. CheckPure.
    (* r'-cells are corrupted *)
    + eapply step0_obs_sbf in H15; try CheckPure. SimpS.
      assert (D: Dtr1_r' (ibs1 i1 i0) (obs1 o1 o0) c0 c1 c2
                       (globcir (false,false,false) cbs1 (ibs1 i1 i0) x45 (obs1 o1 o0)))
          by (constructor; try easy).
      eapply step_Dtr1_r' in D; try exact S3; try exact SS2; try easy. SimpS.
      split. easy.
      eapply eightsteps. 2:exact H15. 2:exact S3. 2:exact S4. 2:exact S5. 2:exact S6.
                         2: exact SS3. 2:exact SS4. 2:exact SS5. 2:exact SS6. 2:exact SS7.
                         2:exact SS8. 2:exact SS9. 2: exact SS10. CheckPure.
    (* output and fail are corrupted *)
    + Apply step_obs_ibf in H15. SimpS.
      Apply invstepDTRc in SS2. SimpS.
      assert (X: corrupt_1in3_bus (~0) {bool2bset b', bool2bset b'0, bool2bset b'1}
              \/ corrupt_1in3_bus (~1) {bool2bset b', bool2bset b'0, bool2bset b'1})
          by (destruct b'; destruct b'0; destruct b'1;
              try (right; constructor); try (left; constructor)).
      destruct X as [X|X].
      * Apply step1_tcbv_i in H17. SimpS.
        Apply step_ibs in H16; try apply pure_buildBus. SimpS.
        Apply step1_mb_d with H13 S2 in H18. SimpS.
        Apply step_obs_sf in H19. SimpS.
        Apply invstepDTRc in SS3. SimpS.
        Apply step0_tcbv_C with H25 in H18. SimpS.
        apply step_ibs in H16; try apply pure_buildBus; try easy. SimpS.
        Apply step0_mb_d' with H17 S3 in H19.
        destruct H19 as [G|G]; SimpS.
        { Apply step_obs_sf in H21. SimpS.
          case_eq (beq_buset_t o1 x29); intro E; rewrite E in H22; Inverts H22.
          - apply beq_buset_imp_eq in E. subst.
            assert (D: Dtrs1 (ibs1 i2 i1) (obs1 o2 x29) c1 c2 c3
                        (globcir (false,false,false) cbs1 (ibs1 i2 i1) x49 (obs1 o2 x29)))
                by (constructor; try easy).
            Apply step_Dtrs1 with S3 SS4 in D. SimpS.
            split. easy. split. easy.
            eapply sixsteps. 2: exact H19. 2: exact S4. 2: exact S5. 2: exact S6.
                             2: exact SS5. 2: exact SS6. 2: exact SS7. 2:exact SS8.
                             2:exact SS9. 2:exact SS10. CheckPure.
          - apply dtrs1_imp_dtr1_d  in H18.
            assert (D: Dtr1_df (ibs1 i2 i1) (dtrOB_T o2 o1 o2 o1 x29) c1 c2 c3
                        (globcir (true,true,true) cbs1 (ibs1 i2 i1) x49 (dtrOB_T o2 o1 o2 o1 x29)))
                by (constructor; try easy). split. easy.
            eapply case1_df. 2: exact D. 2:exact S2. 2: exact S3.
                             2:exact S4. 2:exact S5. 2:exact S6.
                             2:exact SS4. 2:exact SS5. 2:exact SS6.
                             2:exact SS7. 2:exact SS8. 2:exact SS9.
                             2:exact SS10. CheckPure. }
        { Apply step_obs_sf in H21. SimpS. rewrite rew_orS2 in H22. SimpS.
          assert (D: Dtr1_df (ibs1 i2 i1) (dtrOB_T x18 o1 x18 o1 x29) c1 c2 c3
                        (globcir (true,true,true) cbs1 (ibs1 i2 i1) x49 (dtrOB_T x18 o1 x18 o1 x29)))
              by (constructor; try easy). split. easy.
          eapply case1_df. 2: exact D. 2:exact S2. 2: exact S3.
                           2:exact S4. 2:exact S5. 2:exact S6.
                           2:exact SS4. 2:exact SS5. 2:exact SS6.
                           2:exact SS7. 2:exact SS8. 2:exact SS9.
                           2:exact SS10. CheckPure. }
      * Apply stepr1_tcbv_i in H17. SimpS.
        Apply step12_ibs in H16; try apply pure_buildBus. SimpS.
        Apply step1_mb_dF with H13 S1 in H18. SimpS.
        Apply stepr1_obs in H19. SimpS.
        Apply invstepDTRc in SS3. SimpS.
        Apply stepr2_tcbv_C with H35 in H18. SimpS.
        Apply step12_ibs in H16; try apply pure_buildBus. SimpS.
        Apply stepr2_mb_d'rr' with S2 in H19. SimpS.
        Apply stepr23_obs in H21. SimpS.
        assert (D: Dtr3_d'rr' (ibs1 i2 i1) (dtrOB_T o1 o0 o1 o0 x29) c1 c2
                               (globcir (x39,x39,x39) cbs3 (ibs1 i2 i1) x49 (dtrOB_T o1 o0 o1 o0 x29)))
            by (constructor; try easy).
        split. easy.
        eapply case3_d'rr'. 2:exact D. 2:exact S2. 2: exact S3. 2: exact S4.
                            2:exact S5. 2:exact S6. 2:exact SS4. 2:exact SS5.
                            2: exact SS6. 2:exact SS7. 2:exact SS8.
                            2:exact SS9. 2: exact SS10. CheckPure.
   (* fail corrupted *)
    + Apply step_obs_sf in H15. SimpS.
      Apply invstepDTRc in SS2. SimpS.
      assert (X: corrupt_1in3_bus (~0) {bool2bset b', bool2bset b'0, bool2bset b'1}
              \/ corrupt_1in3_bus (~1) {bool2bset b', bool2bset b'0, bool2bset b'1})
          by (destruct b'; destruct b'0; destruct b'1;
              try (right; constructor); try (left; constructor)).
      destruct X as [X|X].
      * Apply step1_tcbv_i in H15. SimpS.
        Apply step_ibs in H; try apply pure_buildBus. SimpS.
        Apply step1_mb_id' with H13 S2 in H16. SimpS.
        Apply step_obs_sf in H17. SimpS.
        Apply invstepDTRc in SS3. SimpS.
        Apply step0_tcbv_C in H16. SimpS.
        Apply step_ibs in H; try apply pure_buildBus. SimpS.
        (* eapply dtr0_d_imp_dr in H2. *)
        Apply step0_mb_dr_F with H15 S3 in H17.
        destruct H17 as [G|G]; SimpS.
        { Apply step_obs_sf in H19. rewrite rew_orS2 in H19. SimpS.
          assert (D: Dtr1_d'rf (ibs1 i2 i1) (dtrOB_T o2 x25 o2 x25 o1) c1 c2 c3
                        (globcir (true,true,true) cbs1 (ibs1 i2 i1) x47 (dtrOB_T o2 x25 o2 x25 o1)))
              by (constructor; try easy).
          Apply step_Dtr1_d'rf with S3 SS4 in D. SimpS.
          Apply step_Dtr2_d'rr' with S4 SS5  in H17. SimpS.
          Apply step_Dtr3_d'rr'' with S4 SS6 in H17. SimpS.
          Apply step_Dtr4_d'rr' with S5 SS7 in H17. SimpS.
          Apply step_Dtr5_d'rr' with SS8 in H17. SimpS.
          Apply step_Dtr0_r' with S6 SS9 in H17. SimpS.
          Apply step_Dtr1_r' with SS10 in H17. SimpS. split; easy. }
        { Apply step_obs_sf in H19. SimpS.
          case_eq (beq_buset_t x25 o1); intro E; rewrite E in H20; Inverts H20.
          - apply beq_buset_imp_eq in E. subst.
            assert (D: Dtr1_r (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                             (globcir (false,false,false) cbs1 (ibs1 i2 i1) x47 (obs1 o2 o1)))
                by (constructor; try easy).
            Apply step_Dtr1_r with S3 SS4 in D. SimpS.
            Apply step_Dtr0_r' with S4 SS5 in H17. SimpS.
            Apply step_Dtr1_r' with S4 SS6 in H17. SimpS.
            split. easy. split. easy. split. easy.
            eapply foursteps. 2: exact H17. 2: exact S5. 2: exact S6.
                              2: exact SS7. 2:exact SS8. 2:exact SS9. 2:exact SS10. CheckPure.
          - Apply dtr1_r_imp_d'r in H16.
            assert (D: Dtr1_d'rf (ibs1 i2 i1) (dtrOB_T o2 x25 o2 x25 o1) c1 c2 c3
                        (globcir (true,true,true) cbs1 (ibs1 i2 i1) x47 (dtrOB_T o2 x25 o2 x25 o1)))
                by (constructor; try easy).
            Apply step_Dtr1_d'rf with S3 SS4 in D. SimpS.
            Apply step_Dtr2_d'rr' with S4 SS5  in H17. SimpS.
            Apply step_Dtr3_d'rr'' with S4 SS6 in H17. SimpS.
            Apply step_Dtr4_d'rr' with S5 SS7 in H17. SimpS.
            Apply step_Dtr5_d'rr' with SS8 in H17. SimpS.
            Apply step_Dtr0_r' with S6 SS9 in H17. SimpS.
            Apply step_Dtr1_r' with SS10 in H17. SimpS.
            split; easy. }
      * Apply stepr1_tcbv_i in H15. SimpS.
        Apply step12_ibs in H; try apply pure_buildBus. SimpS.
        Apply dtr1_d'_imp_d'r in H13.
        Apply step1_mb_d'r with H13 S1 in H16. SimpS.
        Apply stepr1_obs in H17. SimpS.
        Apply invstepDTRc in SS3. SimpS.
        Apply stepr2_tcbv_C in H16. SimpS.
        Apply step12_ibs in H; try apply pure_buildBus. SimpS.
        eapply dtrec_rr'_imp_d'rr' in H15.
        Apply stepr2_mb_d'rr' with S2 in H17. SimpS.
        Apply stepr23_obs in H19. SimpS.
        assert (D: Dtr3_d'rr' (ibs1 i2 i1) (dtrOB_T o1 o0 o1 o0 o1) c1 c2
                               (globcir (x36,x36,x36) cbs3 (ibs1 i2 i1) x46 (dtrOB_T o1 o0 o1 o0 o1)))
            by (constructor; try easy).
        split. easy.
        eapply case3_d'rr'. 2:exact D.  2:exact S2. 2: exact S3. 2: exact S4.
                            2:exact S5. 2:exact S6. 2:exact SS4. 2:exact SS5.
                            2: exact SS6. 2:exact SS7. 2:exact SS8.
                            2:exact SS9. 2: exact SS10. CheckPure.
   (* Glitch occuring within the output buffers *)
  - unfold PexInvDTR5 in H. SimpS.
    Apply step0_tcbv in H13. SimpS.
    Apply step_ibs in H; try apply pure_buildBus. SimpS.
    Purestep H14.
    Apply step0_mb with D S2 in H14. SimpS.
    Apply stepg0_obs in H15. SimpS.
    destruct H13 as [?|[?|?]]; SimpS.
    + assert (D1: Dtrs1 (ibs1 i1 i0) (dtrOB_T o1 x24 o1 o0 o0) c0 c1 c2
                       (globcir (false,false,false) cbs1 (ibs1 i1 i0) x45 (dtrOB_T o1 x24 o1 o0 o0)))
                by (constructor; try easy).
      Apply step_Dtr1 with S2 SS2 in D1. SimpS. split. easy.
      eapply eightsteps. 2:exact H14. 2:exact S3. 2:exact S4. 2:exact S5. 2:exact S6.
                         2: exact SS3. 2:exact SS4. 2:exact SS5. 2:exact SS6. 2:exact SS7.
                         2:exact SS8. 2:exact SS9. 2: exact SS10. CheckPure.
    + Apply invstepDTRc in SS2. SimpS.
      assert (X: corrupt_1in3_bus (~0) {bool2bset b', bool2bset b'0, bool2bset b'1}
              \/ corrupt_1in3_bus (~1) {bool2bset b', bool2bset b'0, bool2bset b'1})
          by (destruct b'; destruct b'0; destruct b'1;
              try (right; constructor); try (left; constructor)).
      destruct X as [X|X].
      * Apply step1_tcbv_i in H14. SimpS.
        Apply step_ibs in H13; try apply pure_buildBus. SimpS.
        Apply step1_mb with H18 S2 in H15. SimpS.
        Apply step_obs_sf in H17. SimpS.
        apply invstepDTRc in SS3; try CheckPure. SimpS.
        Apply step0_tcbv_C with H34 in H15. SimpS.
        Apply step_ibs in H13; try apply pure_buildBus. SimpS.
        Apply step0_mb with H14 S3 in H17. SimpS.
        Apply step0_obs_sbf in H20. SimpS.
        assert (D1: Dtrs1 (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                       (globcir (false,false,false) cbs1 (ibs1 i2 i1) x47 (obs1 o2 o1)))
                by (constructor; try easy).
        Apply step_Dtrs1 with S3 SS4 in D1. SimpS.
        split. easy. split. easy.
        eapply sixsteps. 2: exact H17. 2: exact S4. 2: exact S5. 2: exact S6.
                         2: exact SS5. 2: exact SS6. 2: exact SS7. 2:exact SS8.
                         2:exact SS9. 2:exact SS10. CheckPure.
      * Apply stepr1_tcbv_i in H14. SimpS.
        Apply step12_ibs in H13; try apply pure_buildBus. SimpS.
        eapply dtrs1_imp_dtr1_d in H18.
        Apply step1_mb_dF with H18 S1 in H15. SimpS.
        Apply stepr1_obs in H17. SimpS.
        Apply invstepDTRc in SS3. SimpS.
        Apply stepr2_tcbv_C in H15. SimpS.
        Apply step12_ibs in H13; try apply pure_buildBus. SimpS.
        Apply stepr2_mb_d'rr' with S2 in H17. SimpS.
        Apply stepr23_obs in H20. SimpS.
        assert (D1: Dtr3_d'rr' (ibs1 i2 i1) (dtrOB_T o1 o0 o1 o0 o1) c1 c2
                               (globcir (x36,x36,x36) cbs3 (ibs1 i2 i1) x47 (dtrOB_T o1 o0 o1 o0 o1)))
            by (constructor; try easy).
        split. easy.
        eapply case3_d'rr'. 2:exact D1.  2:exact S2. 2: exact S3. 2: exact S4.
                            2:exact S5. 2:exact S6. 2:exact SS4. 2:exact SS5.
                            2: exact SS6. 2:exact SS7. 2:exact SS8.
                            2:exact SS9. 2: exact SS10. CheckPure.
    + Apply invstepDTRc in SS2. SimpS.
      assert (X: corrupt_1in3_bus (~0) {bool2bset b', bool2bset b'0, bool2bset b'1}
              \/ corrupt_1in3_bus (~1) {bool2bset b', bool2bset b'0, bool2bset b'1})
          by (destruct b'; destruct b'0; destruct b'1;
              try (right; constructor); try (left; constructor)).
      destruct X as [X|X].
      * Apply step1_tcbv_i in H14. SimpS.
        Apply step_ibs in H13; try apply pure_buildBus. SimpS.
        Apply step1_mb with H18 S2 in H15. SimpS.
        Apply step_obs_sf in H17. SimpS.
        Apply invstepDTRc in SS3. SimpS.
        Apply step0_tcbv_C with H34 in H15. SimpS.
        Apply step_ibs in H13; try apply pure_buildBus. SimpS.
        Apply step0_mb with H14 S3 in H17. SimpS.
        Apply step0_obs_sbf in H20. SimpS.
        assert (D1: Dtrs1 (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                       (globcir (false,false,false) cbs1 (ibs1 i2 i1) x47 (obs1 o2 o1)))
                by (constructor; try easy).
        Apply step_Dtrs1 with S3 SS4 in D1. SimpS.
        split. easy. split. easy.
        eapply sixsteps. 2: exact H17. 2: exact S4. 2: exact S5. 2: exact S6.
                         2: exact SS5. 2: exact SS6. 2: exact SS7. 2:exact SS8.
                         2:exact SS9. 2:exact SS10. CheckPure.
      * Apply stepr1_tcbv_i in H14. SimpS.
        Apply step12_ibs in H13; try apply pure_buildBus. SimpS.
        eapply dtrs1_imp_dtr1_d in H18.
        Apply step1_mb_dF with H18 S1 in H15. SimpS.
        Apply stepr1_obs in H17. SimpS.
        Apply invstepDTRc in SS3. SimpS.
        Apply stepr2_tcbv_C with H34 in H15. SimpS.
        Apply step12_ibs in H13; try apply pure_buildBus. SimpS.
        Apply stepr2_mb_d'rr' with S2 in H17. SimpS.
        Apply stepr23_obs in H20. SimpS.
        assert (D1: Dtr3_d'rr' (ibs1 i2 i1) (dtrOB_T o1 o0 o1 o0 o1) c1 c2
                               (globcir (x36,x36,x36) cbs3 (ibs1 i2 i1) x47 (dtrOB_T o1 o0 o1 o0 o1)))
            by (constructor; try easy).
        split. easy.
        eapply case3_d'rr'. 2:exact D1.  2:exact S2. 2: exact S3. 2: exact S4.
                            2:exact S5. 2:exact S6. 2:exact SS4. 2:exact SS5.
                            2: exact SS6. 2:exact SS7. 2:exact SS8.
                            2:exact SS9. 2: exact SS10. CheckPure.
Qed.

