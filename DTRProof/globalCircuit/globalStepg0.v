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
Require Import globalInv globalLem0 globalSeqs.

Set Implicit Arguments.

(* ------------------------------------------------------- *)

Lemma stepg_In0: forall S T (i0 i1 i2 i3 i4 i5: {|S|}) 
                           (o o0 o1 o2 o3 o4 o5: {|T|})
                           (oo0 oo1 oo2 oo3 oo4 oo5 oo6 oo7 oo8 oo9:{|T # (T # T)|})
                           (c0 c1 c2 c3 c4 c5 c6: circuit S T)
                           (cc1 cc1' cc2 cc2' cc3 cc3' cc4 cc4' cc5 cc5' cc6: circuit S (T # (T # T))),
                pure_bset {i0,i1,i2,i3,i4,i5,o,o0,o1,o2,o3,o4,o5}
             -> Dtrs0 (ibs0 i0) (obs0 o0 o) c0 c1 cc1
             -> step c0 i0 o0 c1
             -> step c1 i1 o1 c2
             -> step c2 i2 o2 c3
             -> step c3 i3 o3 c4
             -> step c4 i4 o4 c5
             -> step c5 i5 o5 c6
             -> stepg cc1 i1 oo0 cc1'
             -> step  cc1' i1 oo1 cc2
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
introv P D S1 S2 S3 S4 S5 S6.
introv SS1 SS2 SS3 SS4 SS5 SS6 SS7 SS8 SS9 SS10. SimpS.
Inverts D. Inverts SS1. Inverts H20. Inverts H23.
(* Glitch occuring inside *)
- eapply glitch0_in_GC. 2:exact H21. 2:exact H19. 2:exact H22. 2:exact H20. 
                        2: exact S1. 2: exact S2. 2:exact S3. 2:exact S4. 2:exact S5. 
                        2:exact S6. 2:exact SS2. 2:exact SS3. 2:exact SS4.
                        2:exact SS5. 2:exact SS6. 2:exact SS7. 2:exact SS8.
                        2:exact SS9. 2:exact SS10. 2:exact H24. CheckPure.
  (* possible glitch in the triplicated fail signal to control block *)
- eapply glitch0_in_3fail. 2: exact H21.  2: exact H19. 2: exact H22. 2: exact H24. 
                           2: exact H20.  2: exact S2. 2: exact S3. 2: exact S4. 
                           2: exact S5.  2: exact S6. 2: exact SS2. 2: exact SS3. 
                           2: exact SS4.  2: exact SS5. 2: exact SS6. 2: exact SS7. 
                           2: exact SS8.  2: exact SS9. 2: exact SS10. 2: exact H25. CheckPure.
- Inverts H24. 
  eapply invstepcore in H25; try easy. 
  unfold PexInvDTR1 in H25. SimpS.
  eapply step0_tcbv_i with (fI:=bool2bset f) in H13; try CheckPure. SimpS. 
  Apply step_ibs in H12; try apply pure_buildBus. SimpS. 
  Purestep H14. Apply step0_mb with H21 S2 in H14. SimpS. 
  Purestep H15. Apply step0_obs_sbf in H15. SimpS. 
  Apply invstepDTRc in SS2. SimpS. 
  Apply step1_tcbv_C in H13. SimpS. 
  Apply step_ibs in H12; try apply pure_buildBus. SimpS. 
  Apply step1_mb with H24 S2 in H14. SimpS. 
  Apply step_obs_sf in H15. SimpS. 
  assert (D: Dtrs0 (ibs0 i1) (obs0 o1 o0) c1 c2
                   (globcir (x37,x37,x37) cbs0 (ibs0 i1) x44 (obs0 o1 o0)))
      by (constructor; try easy).
  split. easy.
  eapply eightsteps. 2:exact D. 2:exact S3. 2:exact S4. 2:exact S5.  2:exact S6.
                     2:exact SS3. 2: exact SS4. 2:exact SS5. 2:exact SS6. 2:exact SS7.
                     2:exact SS8. 2:exact SS9. 2: exact SS10. CheckPure.
- Inverts H22. Inverts H24. 
  eapply invstepcore in H25; try easy. 
  unfold PexInvDTR1 in H25. SimpS.
  eapply step0_tcbv_i with (fI:=bool2bset f) in H13; try CheckPure. SimpS.
  Apply step_ibs in H12; try apply pure_buildBus. SimpS.
  Purestep H14. Apply step0_mb with H21 S2 in H14. SimpS.
  Purestep H15. Apply step0_obs_sbf in H15. SimpS.
  Apply invstepDTRc in SS2. SimpS.
  Apply step1_tcbv_C in H13. SimpS.
  Apply step_ibs in H12; try apply pure_buildBus. SimpS.
  Apply step1_mb with H24 S2 in H14. SimpS.
  Apply step_obs_sf in H15. SimpS.
  assert (D: Dtrs0 (ibs0 i1) (obs0 o1 o0) c1 c2
                   (globcir (x37,x37,x37) cbs0 (ibs0 i1) x44 (obs0 o1 o0)))
      by (constructor; try easy).
  split. easy.
  eapply eightsteps. 2:exact D. 2:exact S3. 2:exact S4. 2:exact S5.  2:exact S6.
                     2:exact SS3. 2: exact SS4. 2:exact SS5. 2:exact SS6. 2:exact SS7.
                     2:exact SS8. 2:exact SS9. 2: exact SS10. CheckPure.
Qed.
