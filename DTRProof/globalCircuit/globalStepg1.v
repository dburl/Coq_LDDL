(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
- Main properties and theorem

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
Require Import inputLib controlLib outputLib memoryLib.
Require Import globalInv globalStep globalLem1 globalSeqs.

Set Implicit Arguments.

(* ------------------------------------------------------- *)

Lemma stepg_In1: forall S T (i0 i1 i2 i3 i4 i5: {|S|}) 
                           (o0 o1 o2 o3 o4 o5: {|T|})
                           (oo1 oo2 oo3 oo4 oo5 oo6 oo7 oo8 oo9:{|T # (T # T)|})
                           (c0 c1 c2 c3 c4 c5 c6: circuit S T)
                           (cc1 cc2 cc2' cc3 cc3' cc4 cc4' cc5 cc5' cc6: circuit S (T # (T # T))),
                pure_bset {i0,i1,i2,i3,i4,i5,o0,o1,o2,o3,o4,o5}
             -> Dtrs1 (ibs1 i1 i0) (obs1 o1 o0) c0 c1 c2 cc1
             -> step c1 i1 o1 c2
             -> step c2 i2 o2 c3
             -> step c3 i3 o3 c4
             -> step c4 i4 o4 c5
             -> step c5 i5 o5 c6
             -> stepg cc1 i1 oo1 cc2
             -> step  cc2  i2 oo2 cc2'
             -> step  cc2' i2 oo3 cc3
             -> step  cc3  i3 oo4 cc3'
             -> step  cc3' i3 oo5 cc4
             -> step  cc4  i4 oo6 cc4'
             -> step  cc4' i4 oo7 cc5
             -> step  cc5  i5 oo8 cc5'
             -> step  cc5' i5 oo9 cc6
             -> atleast2 o0 oo1
             /\ atleast2 o1 oo3
             /\ atleast2 o2 oo5
             /\ atleast2 o3 oo7
             /\ atleast2 o4 oo9
             /\ Dtrs0 (ibs0 i5) (obs0 o5 o4) c5 c6 cc6.
Proof.
introv P D (* S1 *) S2 S3 S4 S5 S6.
introv SS1 SS2 SS3 SS4 SS5 SS6 SS7 SS8 SS9. SimpS.
Inverts D. Inverts SS1. Inverts H19. Inverts H21.
(* Glitch occuring inside *)
- eapply glitch_in_GC.  2:exact H22. 2:exact H18. 2:exact H20. 2:exact H19. 
                        2: exact S2. 2:exact S3. 2:exact S4. 2:exact S5. 
                        2:exact S6. 2:exact SS2. 2:exact SS3. 2:exact SS4.
                        2:exact SS5. 2:exact SS6. 2:exact SS7. 2:exact SS8.
                        2:exact SS9. 2:exact H23. CheckPure.
  (* possible glitch in the triplicated fail signal to control block *)
- eapply glitch_in_3fail. 2: exact H22. 2: exact H18. 2: exact H20. 2: exact H23. 
                          2: exact H19.  2: exact S2. 2: exact S3. 2: exact S4. 
                          2: exact S5.  2: exact S6. 2: exact SS2. 2: exact SS3. 
                          2: exact SS4.  2: exact SS5. 2: exact SS6. 2: exact SS7. 
                          2: exact SS8.  2: exact SS9. 2: exact H24. CheckPure.
- Inverts H23. 
  eapply invstepcore in H24; try easy. 
  unfold PexInvDTR1 in H24. SimpS.
  Inverts H20. 
  + eapply step1_tcbv_i in H12; try (solve [constructor]). SimpS.
    Apply step_ibs in H11; try apply pure_buildBus. SimpS. Purestep H13. 
    Apply step1_mb with H22 S2 in H13. SimpS. Purestep H14. 
    Apply step_obs_sf in H14. SimpS.
    Apply invstepDTRc in SS2. SimpS.
    Apply step0_tcbv_C in H14. SimpS.
    Apply step_ibs in H11; try apply pure_buildBus. SimpS.
    Apply step0_mb with H20 S3 in H18. SimpS. 
    Apply step0_obs_sbf in H21. SimpS.
    assert (D: Dtrs1 (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                    (globcir (false,false,false) cbs1 (ibs1 i2 i1) x43 (obs1 o2 o1)))
        by (constructor; try easy).
    Apply step_Dtrs1 with S3 SS3 in D. SimpS.
    split. easy. split. easy.
    eapply sixsteps. 2:exact H18. 2:exact S4. 2:exact S5. 2:exact S6.
                     2:exact SS4. 2:exact SS5. 2:exact SS6. 2:exact SS7.
                     2:exact SS8. 2:exact SS9. CheckPure.
      (* no glitch *)
  + eapply step1_tcbv in H12; try (solve [constructor]). SimpS.
    Apply step_ibs in H11; try apply pure_buildBus. SimpS.
    Apply step1_mb with H22 S2 in H13. SimpS.
    Apply step_obs_sf in H14. 
    assert (X: pure_bset (orS {bool2bset x21, bool2bset (negb (beq_buset_t o1 o0))}))
        by (Apply pure_orS). SimpS. 
    assert (D: Dtrs0 (ibs0 i1) (obs0 o1 o0) c1 c2 
                     (globcir (b',b',b') cbs0 (ibs0 i1) x42 (obs0 o1 o0)))
        by (constructor; try easy).
    split. easy.
    eapply eightsteps. 2:exact D. 2:exact S3. 2:exact S4. 2:exact S5. 2:exact S6.
                       2: exact SS2. 2:exact SS3. 2:exact SS4. 2:exact SS5. 
                       2:exact SS6. 2:exact SS7. 2:exact SS8. 2:exact SS9. CheckPure.
- Inverts H20. Inverts H23. 
  Apply invstepcore in H24. 
  unfold PexInvDTR1 in H24. SimpS.
  Inverts H18. 
  + eapply step1_tcbv_i in H12; try (solve [constructor]). SimpS.
    Apply step_ibs in H11; try apply pure_buildBus. SimpS. Purestep H13. 
    Apply step1_mb with H22 S2 in H13. SimpS. Purestep H14. 
    Apply step_obs_sf in H14. SimpS. 
    Apply invstepDTRc in SS2. SimpS.
    Apply step0_tcbv_C in H14. SimpS.
    Apply step_ibs in H11; try apply pure_buildBus. SimpS.
    Apply step0_mb with H18 S3 in H19. SimpS.
    Apply step0_obs_sbf in H21. SimpS.
    assert (D: Dtrs1 (ibs1 i2 i1) (obs1 o2 o1) c1 c2 c3
                    (globcir (false,false,false) cbs1 (ibs1 i2 i1) x43 (obs1 o2 o1)))
        by (constructor; try easy).
    Apply step_Dtrs1 with S3 SS3 in D. SimpS.
    split. easy. split. easy.
    eapply sixsteps. 2:exact H19. 2:exact S4. 2:exact S5. 2:exact S6.
                     2:exact SS4. 2:exact SS5. 2:exact SS6. 2:exact SS7.
                     2:exact SS8. 2:exact SS9. CheckPure.
  + (* no glitch *)
    eapply step1_tcbv in H12; try (solve [constructor]). SimpS.
    Apply step_ibs in H11; try apply pure_buildBus. SimpS.
    Apply step1_mb with H22 S2 in H13. SimpS.
    Apply step_obs_sf in H14. 
    assert (X: pure_bset (orS {bool2bset x21, bool2bset (negb (beq_buset_t o1 o0))}))
        by (Apply pure_orS). SimpS. 
    assert (D: Dtrs0 (ibs0 i1) (obs0 o1 o0) c1 c2 
                     (globcir (b',b',b') cbs0 (ibs0 i1) x42 (obs0 o1 o0)))
        by (constructor; try easy).
    split. easy.
    eapply eightsteps. 2:exact D. 2:exact S3. 2:exact S4. 2:exact S5. 2:exact S6.
                       2: exact SS2. 2:exact SS3. 2:exact SS4. 2:exact SS5. 
                       2:exact SS6. 2:exact SS7. 2:exact SS8. 2:exact SS9. CheckPure.
Qed.
