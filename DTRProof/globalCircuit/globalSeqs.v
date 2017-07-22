(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
A lew lemmas for common reduction case
used several times in the global lemmas 

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

Require Import dtrTransform relationPred globalInv globalStep inputLib controlLib outputLib memoryLib. 

Set Implicit Arguments.

(* ------------------------------------------------------- *)

(* At least 2 buses in a triplicated version are correct (equal to the bus argument) *)
(* Used in the main lemmas and the final correctness property                        *)

Inductive atleast2 : forall S, {|S|} -> {|S#(S#S)|} -> Prop :=
| Al2_1 : forall S (s t:{|S|}), atleast2 s {s,{s,t}}
| Al2_2 : forall S (s t:{|S|}), atleast2 s {s,{t,s}}
| Al2_3 : forall S (s t:{|S|}), atleast2 s {t,{s,s}}.
Hint Constructors atleast2.

(* Cases of reduction occurring several times in step(g) reduction of the complete transformed circuit *)

Lemma case1_df : forall S T (i1 i2 i3 i4 i5: {|S|}) (o1 o2 o3 o4 o5 y z: {|T|}) 
                             oo3 oo4 oo5 oo6 oo7 oo8 oo9
                            (c1 c2 c3 c4 c5 c6: circuit S T) 
                        (cc2' cc3 cc3' cc4 cc4' cc5 cc5' cc6: circuit S (T # (T # T))),
                 pure_bset {i1,i2,i3,i4,i5,o1,o2,o3,o4,o5,y,z}
              -> Dtr1_df (ibs1 i2 i1) (dtrOB_T z o1 z o1 y) c1 c2 c3 cc2'
              -> step c1 i1 o1 c2
              -> step c2 i2 o2 c3
              -> step c3 i3 o3 c4
              -> step c4 i4 o4 c5
              -> step c5 i5 o5 c6
              -> step cc2' i2 oo3 cc3    
              -> step cc3  i3 oo4 cc3'
              -> step cc3' i3 oo5 cc4
              -> step cc4  i4 oo6 cc4'
              -> step cc4' i4 oo7 cc5 
              -> step cc5  i5 oo8 cc5'
              -> step cc5' i5 oo9 cc6
              -> atleast2 o1 oo3
              /\ atleast2 o2 oo5
              /\ atleast2 o3 oo7
              /\ atleast2 o4 oo9
              /\  Dtrs0 (ibs0 i5) (obs0 o5 o4) c5 c6 cc6.
Proof.
introv P D S2 S3 S4 S5 S6.
introv SS4 SS5 SS6 SS7 SS8 SS9 SS10. SimpS.
Apply step_Dtr1_df with S2 S3 SS4 in D. SimpS. 
Apply step_Dtr2_d'rr'' with S3 S4 SS5 in H12. SimpS. 
Apply step_Dtr3_d'rr'' with S4 SS6 in H12. SimpS.
Apply step_Dtr4_d'rr' with S5 SS7 in H12. SimpS. 
Apply step_Dtr5_d'rr' with SS8 in H12. SimpS. 
Apply step_Dtr0_r' with S6 SS9 in H12. SimpS. 
Apply step_Dtr1_r' with SS10 in H12. SimpS. split; easy.
Qed.

Lemma case3_d'rr' : forall S T (i1 i2 i3 i4 i5: {|S|}) (o0 o1 o2 o3 o4 o5 x: {|T|}) 
                             oo3 oo4 oo5 oo6 oo7 oo8 oo9
                            (c1 c2 c3 c4 c5 c6: circuit S T) 
                        (cc2' cc3 cc3' cc4 cc4' cc5 cc5' cc6: circuit S (T # (T # T))),
                 pure_bset {i1,i2,i3,i4,i5,o0,o1,o2,o3,o4,o5,x}
              -> Dtr3_d'rr' (ibs1 i2 i1) (dtrOB_T o1 o0 o1 o0 x) c1 c2 cc2'
              -> step c1 i1 o1 c2
              -> step c2 i2 o2 c3
              -> step c3 i3 o3 c4
              -> step c4 i4 o4 c5
              -> step c5 i5 o5 c6
              -> step cc2' i2 oo3 cc3    
              -> step cc3  i3 oo4 cc3'
              -> step cc3' i3 oo5 cc4
              -> step cc4  i4 oo6 cc4'
              -> step cc4' i4 oo7 cc5 
              -> step cc5  i5 oo8 cc5'
              -> step cc5' i5 oo9 cc6
              -> atleast2 o1 oo3
              /\ atleast2 o2 oo5
              /\ atleast2 o3 oo7
              /\ atleast2 o4 oo9
              /\  Dtrs0 (ibs0 i5) (obs0 o5 o4) c5 c6 cc6.
Proof.
introv P D S2 S3 S4 S5 S6.
introv SS4 SS5 SS6 SS7 SS8 SS9 SS10. SimpS.
Apply step_Dtr3_d'rr'' with S3 SS4 in D. SimpS.
Apply step_Dtr4_d'rr' with S4 SS5 in H12. SimpS.
Apply step_Dtr5_d'rr' with S4 SS6 in H12. SimpS.
Apply step_Dtr0_r' with S5 SS7 in H12. SimpS.
Apply step_Dtr1_r' with S5 SS8 in H12. SimpS.
Apply step_Dtrs0 with S6 SS9 in H12. SimpS.
Apply step_Dtrs1 with S6 SS10 in H12. SimpS.
split; easy.
Qed.


Lemma case0_dr : forall S T (i0 i1 i2 i3 i4: {|S|}) 
                           (o o0 o1 o2 o3 o4 z1 z2: {|T|})
                           (oo1 oo2 oo3 oo4 oo5 oo6 oo7 oo8:{|T # (T # T)|})
                           (c0 c1 c2 c3 c4 c5: circuit S T)
                           (cc1' cc2 cc2' cc3 cc3' cc4 cc4' cc5: circuit S (T # (T # T))) cc1 f f' f'',
                pure_bset {i0,i1,i2,i3,i4,o,o0,o1,o2,o3,o4,z1,z2}
             -> dtr0_dr c0 c1 cc1
             -> step c0 i0 o0 c1
             -> step c1 i1 o1 c2
             -> step c2 i2 o2 c3
             -> step c3 i3 o3 c4
             -> step c4 i4 o4 c5
             -> step (-{f}-(-{f'}-(-{f''}-dtrcore (ibs0 i0) cbs0 cc1 (dtrOB_T z1 o0 z2 o0 o)))) i1 oo1 cc1'
             -> step cc1' i1 oo2 cc2
             -> step cc2  i2 oo3 cc2'
             -> step cc2' i2 oo4 cc3
             -> step cc3  i3 oo5 cc3'
             -> step cc3' i3 oo6 cc4
             -> step cc4  i4 oo7 cc4'
             -> step cc4' i4 oo8 cc5
             -> atleast2 o0 oo2
             /\ atleast2 o1 oo4
             /\ atleast2 o2 oo6
             /\ atleast2 o3 oo8
             /\ Dtrs0 (ibs0 i4) (obs0 o4 o3) c4 c5 cc5.
Proof.
introv P D S1 S2 S3 S4 S5.
introv SS1 SS2 SS3 SS4 SS5 SS6 SS7 SS8. SimpS.
Apply invstepDTRc in SS1. SimpS.
Apply step0_tcbv in H13. SimpS. 
Apply step_ibs in H12; try apply pure_buildBus. SimpS.
Apply step0_mb_dr_F with D S2 in H14.
destruct H14 as [X1|X1]; SimpS.
- Apply step_obs_sf in H15. SimpS. 
  rewrite rew_orS2 in H16. Inverts H16.
  assert (D1: Dtr1_d'rf (ibs1 i1 i0) (dtrOB_T o1 z1 o1 z2 o0) c0 c1 c2 
                     (globcir (true,true,true) cbs1 (ibs1 i1 i0) x40 (dtrOB_T o1 z1 o1 z2 o0))) 
      by (constructor; try easy).  
  Apply step_Dtr1_d'rf with SS2 in D1. SimpS.
  Apply step_Dtr2_d'rr' with S2 S3 SS3 in H14. SimpS. 
  Apply step_Dtr3_d'rr' with S3 SS4 in H14. SimpS.
  Apply step_Dtr4_d'rr' with S4 SS5 in H14. SimpS. 
  Apply step_Dtr5_d'rr' with SS6 in H14. SimpS.
  Apply step_Dtr0_r' with S5 SS7 in H14. SimpS. 
  Apply step_Dtr1_r' with S5 SS8 in H14. SimpS.
  split; easy.
- Apply step_obs_sf in H15. SimpS.
  case_eq (beq_buset_t z2 o0); intro E; rewrite E in H16; Inverts H16.
  + apply beq_buset_imp_eq in E. subst.
    assert (D1: Dtr1_r (ibs1 i1 i0) (dtrOB_T o1 z1 o1 o0 o0) c0 c1 c2 
                     (globcir (false,false,false) cbs1 (ibs1 i1 i0) x40 (dtrOB_T o1 z1 o1 o0 o0))) 
        by (constructor; try easy).  
    Apply step_Dtr1_r with SS2 in D1. SimpS.
    Apply step_Dtr0_r' with S3 SS3 in H14. SimpS.
    Apply step_Dtr1_r' with SS4 in H12. SimpS.
    Apply step_Dtrs0 with S4 SS5 in H12. SimpS.
    Apply step_Dtrs1 with SS6 in H12. SimpS.
    Apply step_Dtrs0 with S5 SS7 in H12. SimpS.
    Apply step_Dtrs1 with SS8 in H12. SimpS. 
    split; easy.
  + apply dtr1_r_imp_d'r in H13.
    assert (D1: Dtr1_d'rf (ibs1 i1 i0) (dtrOB_T o1 z1 o1 z2 o0) c0 c1 c2 
                     (globcir (true,true,true) cbs1 (ibs1 i1 i0) x40 (dtrOB_T o1 z1 o1 z2 o0))) 
        by (constructor; try easy).  
    Apply step_Dtr1_d'rf with SS2 in D1. SimpS.
    Apply step_Dtr2_d'rr' with S3 SS3 in H14. SimpS. 
    Apply step_Dtr3_d'rr' with S3 SS4 in H14. SimpS.
    Apply step_Dtr4_d'rr' with S4 SS5 in H14. SimpS. 
    Apply step_Dtr5_d'rr' with SS6 in H14. SimpS. 
    Apply step_Dtr0_r' with S5 SS7 in H14. SimpS. 
    Apply step_Dtr1_r' with S5 SS8 in H14. SimpS. 
    split; easy.
Qed.

Lemma foursteps: forall S T (i3 i4 i5: {|S|}) 
                           (o2 o3 o4 o5: {|T|})
                           (oo6 oo7 oo8 oo9:{|T # (T # T)|})
                           (c3 c4 c5 c6: circuit S T)
                           (cc4 cc4' cc5 cc5' cc6: circuit S (T # (T # T))),
                pure_bset {i3,i4,i5,o2,o3,o4,o5}
             -> Dtrs0 (ibs0 i3) (obs0 o3 o2) c3 c4 cc4
             -> step c4 i4 o4 c5
             -> step c5 i5 o5 c6
             -> step cc4  i4 oo6 cc4'
             -> step cc4' i4 oo7 cc5
             -> step cc5  i5 oo8 cc5'
             -> step cc5' i5 oo9 cc6
             -> atleast2 o3 oo7
             /\ atleast2 o4 oo9
             /\ Dtrs0 (ibs0 i5) (obs0 o5 o4) c5 c6 cc6.
Proof.
introv P D S5 S6.
introv SS6 SS7 SS8 SS9. SimpS.
Apply step_Dtrs0 with S5 SS6 in D. SimpS.
Apply step_Dtrs1 with S5 SS7 in H7. SimpS.
Apply step_Dtrs0 with S6 SS8 in H7. SimpS.
Apply step_Dtrs1 with S6 SS9 in H7. SimpS.
easy.
Qed.

Lemma sixsteps: forall S T (i2 i3 i4 i5: {|S|}) 
                           (o1 o2 o3 o4 o5: {|T|})
                           (oo4 oo5 oo6 oo7 oo8 oo9:{|T # (T # T)|})
                           (c2 c3 c4 c5 c6: circuit S T)
                           (cc3 cc3' cc4 cc4' cc5 cc5' cc6: circuit S (T # (T # T))),
                pure_bset {i2,i3,i4,i5,o1,o2,o3,o4,o5}
             -> Dtrs0 (ibs0 i2) (obs0 o2 o1) c2 c3 cc3
             -> step c3 i3 o3 c4
             -> step c4 i4 o4 c5
             -> step c5 i5 o5 c6
             -> step cc3  i3 oo4 cc3'
             -> step cc3' i3 oo5 cc4
             -> step cc4  i4 oo6 cc4'
             -> step cc4' i4 oo7 cc5
             -> step cc5  i5 oo8 cc5'
             -> step cc5' i5 oo9 cc6
             -> atleast2 o2 oo5
             /\ atleast2 o3 oo7
             /\ atleast2 o4 oo9
             /\ Dtrs0 (ibs0 i5) (obs0 o5 o4) c5 c6 cc6.
Proof.
introv P D S4 S5 S6.
introv SS4 SS5 SS6 SS7 SS8 SS9. SimpS.
Apply step_Dtrs0 with S4 SS4 in D. SimpS.
Apply step_Dtrs1 with S4 SS5 in H9. SimpS.
split. easy.
eapply foursteps. 2: exact H9. 2: exact S5. 2: exact S6. 2: exact SS6.
                  2: exact SS7. 2: exact SS8. 2: exact SS9. CheckPure. 
Qed.

Lemma eightsteps: forall S T (i1 i2 i3 i4 i5: {|S|}) 
                           (o0 o1 o2 o3 o4 o5: {|T|})
                           (oo2 oo3 oo4 oo5 oo6 oo7 oo8 oo9:{|T # (T # T)|})
                           (c1 c2 c3 c4 c5 c6: circuit S T)
                           (cc2 cc2' cc3 cc3' cc4 cc4' cc5 cc5' cc6: circuit S (T # (T # T))),
                pure_bset {i1,i2,i3,i4,i5,o0,o1,o2,o3,o4,o5}
             -> Dtrs0 (ibs0 i1) (obs0 o1 o0) c1 c2 cc2
             -> step c2 i2 o2 c3
             -> step c3 i3 o3 c4
             -> step c4 i4 o4 c5
             -> step c5 i5 o5 c6
             -> step cc2  i2 oo2 cc2'
             -> step cc2' i2 oo3 cc3
             -> step cc3  i3 oo4 cc3'
             -> step cc3' i3 oo5 cc4
             -> step cc4  i4 oo6 cc4'
             -> step cc4' i4 oo7 cc5
             -> step cc5  i5 oo8 cc5'
             -> step cc5' i5 oo9 cc6
             -> atleast2 o1 oo3
             /\ atleast2 o2 oo5
             /\ atleast2 o3 oo7
             /\ atleast2 o4 oo9
             /\ Dtrs0 (ibs0 i5) (obs0 o5 o4) c5 c6 cc6.
Proof.
introv P D S3 S4 S5 S6.
introv SS2 SS3 SS4 SS5 SS6 SS7 SS8 SS9. SimpS.
eapply foursteps in D. 3: exact S3. 3: exact S4. 3: exact SS2. 3: exact SS3.
                       3: exact SS4. 3: exact SS5. 2: CheckPure. SimpS.
split. easy. split. easy.
eapply foursteps. 2: exact H12. 2: exact S5. 2: exact S6. 2: exact SS6.
                  2: exact SS7. 2: exact SS8. 2: exact SS9. CheckPure. 
Qed.
