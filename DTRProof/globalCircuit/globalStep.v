(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
- Lemmas about the standard reduction of the complete transformed circuit 
 (i.e., with the control block + IO buffers)

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

Require Import dtrTransform relationPred globalInv inputLib controlLib outputLib memoryLib. 

Set Implicit Arguments.

(* ------------------------------------------------------- *)

Lemma step_Dtr0 : forall S T (i1 i2 s:{|S|}) (p p' o o':{|T|}) (c c' c'':circuit S T) (cc cc':circuit S (T#(T#T))) t t3, 
                     pure_bset {i1,i2,p,p',o,o',s} 
                  -> Dtrs0 (dtrIB_T i1 i2) (dtrOB_T p p' o o o') c c' cc 
                  -> step c' s t c''
                  -> step cc s t3 cc' 
                  -> t3={p',{o,o'}} /\ Dtrs1 (ibs1 s i1) (dtrOB_T t p t o o) c c' c'' cc'.
Proof. 
introv P D H1 H2.
SimpS. Inverts D.  
Apply invstepDTRc in H2.
destruct H2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X1[X2[X3[X4[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS. Apply step0_tcbv in X2. SimpS.
Apply step_ibs in X1; try apply pure_buildBus. SimpS.
Apply step0_mb with H1 H17 in X3. SimpS.
replace ({~ 0, ~ 0, ~ 0, ~ 0}) with ({~ 0, ~ 0, bool2bset false, ~ 0}) in X4. 2: easy.
Apply step_obs_sf in X4; try apply pure_buildBus. SimpS.
rewrite beq_buset_reflx in H2. Inverts H2.
split. easy. constructor. easy. 
Qed. 

Lemma step_Dtr1 : forall S T (i s:{|S|}) (p p' o o' o'' t:{|T|}) (c c' c'':circuit S T) (cc cc':circuit S (T#(T#T))) t3, 
                      pure_bset {i,p,p',o,o',o'',s} 
                   -> Dtrs1 (ibs1 s i) (dtrOB_T p p' o o' o'') c c' c'' cc 
                   -> step c' s t c''
                   -> step cc s t3 cc' 
                   -> t3={p',{o',o''}} /\ Dtrs0 (ibs0 s) (dtrOB_T t p t o o') c' c'' cc'.
Proof. 
introv P D H1 H2. SimpS. Inverts D. 
Apply invstepDTRc in H2.
destruct H2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X1[X2[X3[X4[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS. Apply step1_tcbv in X2. SimpS.
Apply step_ibs in X1; try apply pure_buildBus. SimpS.
Apply step1_mb with H1 H19 in X3. SimpS.
Apply step_obs_sf in X4; try apply pure_buildBus. SimpS.
split. easy. constructor. easy.
Qed. 



Lemma step_Dtrs0 : forall S T (i s:{|S|}) (o o':{|T|}) (c c' c'':circuit S T) (cc cc':circuit S (T#(T#T))) t t3, 
                     pure_bset i -> pure_bset o -> pure_bset o' -> pure_bset s 
                  -> Dtrs0 (ibs0 i) (obs0 o o') c c' cc 
                  -> step c' s t c''
                  -> step cc s t3 cc' 
                  -> t3={o,{o,o'}} /\ Dtrs1 (ibs1 s i) (obs1 t o) c c' c'' cc'.
Proof.
introv P1 P2 P3 P4 D H1 H2.
Inverts D.  
Apply invstepDTRc in H2.
destruct H2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X1[X2[X3[X4[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS. Apply step0_tcbv in X2; try CheckPure. SimpS.
Apply step_ibs in X1; try apply pure_buildBus. SimpS.
Apply step0_mb with H1 H10 in X3. SimpS.
Apply step0_obs_sbf in X4; try apply pure_buildBus. SimpS.   
split. easy. constructor. easy. 
Qed.


Lemma step_Dtrs1 : forall S T (i s:{|S|}) (o o':{|T|}) (c c' c'':circuit S T) (cc cc':circuit S (T#(T#T))) t3, 
                      pure_bset i -> pure_bset o -> pure_bset o' -> pure_bset s 
                   -> Dtrs1 (ibs1 s i) (obs1 o o') c c' c'' cc -> step c' s o c''
                   -> step cc s t3 cc' 
                   -> t3={o',{o',o'}} /\ Dtrs0 (ibs0 s) (obs0 o o') c' c'' cc'.
Proof. 
introv P1 P2 P3 P4 D H1 H2.
Inverts D. Apply invstepDTRc in H2.
destruct H2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X1[X2[X3[X4[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS. Apply step1_tcbv in X2. SimpS.
Apply step_ibs in X1; try apply pure_buildBus. SimpS.
Apply step1_mb with H1 H12 in X3. SimpS.
Apply step1_obs_sbf in X4; try apply pure_buildBus. 
SimpS. split. easy. constructor. easy.
Qed. 


Lemma step_Dtr0_d'  : forall S T (i s:{|S|}) (o o' x y:{|T|}) 
                                  (c c' c'':circuit S T) (cc cc':circuit S (T#(T#T))) t t3, 
                      pure_bset {i,s,o,o',x,y,s} 
                   -> Dtr0_d' (ibs0 i) (dtrOB_T o x o y o') c c' cc 
                   -> step c' s t c''
                   -> step cc s t3 cc' 
                   ->  Dtrs1 (ibs1 s i) (dtrOB_T t o t o y) c c' c'' cc'
                    \/ (exists z, pure_bset z
                               /\ Dtr1_df (ibs1 s i) (dtrOB_T z o z o y) c c' c'' cc').
Proof.
introv P D H1 H2. SimpS.
Inverts D. Apply invstepDTRc in H2.
destruct H2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X1[X2[X3[X4[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS. Apply step0_tcbv in X2. SimpS.
Apply step_ibs in X1; try apply pure_buildBus. SimpS.
Apply step0_mb_d' with H1 H16 in X3.
destruct X3 as [X|X]; SimpS.
- Apply step_obs_sf in X4. SimpS. 
  destruct (beq_buset_t o y); Inverts H0.
  + left. constructor. easy.
  + right. exists t. split. easy. constructor.  
    apply dtrs1_imp_dtr1_d. easy.
- Apply step_obs_sf in X4. SimpS.
  right. exists x0. split. easy. 
  destruct (beq_buset_t o y); Inverts H0; constructor; easy.
Qed.   


Lemma step_Dtr0_dr  : forall S T (i s:{|S|}) (x y o o':{|T|}) (c c' c'':circuit S T) (cc cc':circuit S (T#(T#T))) t t3, 
                       pure_bset {i,x,y,o,o',s} 
                    -> Dtr0_dr (ibs0 i) (dtrOB_T x o y o o') c c' cc 
                    -> step c' s t c''
                    -> step cc s t3 cc'
                    -> t3={o,{o,o'}} /\ Dtr1_d'rf (ibs1 s i) (dtrOB_T t x t y o) c c' c'' cc'
                    \/ t3={o,{o,o'}} /\ Dtr1_r (ibs1 s i) (dtrOB_T t x t o o) c c' c'' cc'.
Proof. 
introv P D H1 H2. SimpS.
Inverts D. Apply invstepDTRc in H2.
destruct H2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X1[X2[X3[X4[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS. Apply step0_tcbv in X2. SimpS.
Apply step_ibs in X1; try apply pure_buildBus. SimpS.
Apply step0_mb_dr_F with H1 H16 in X3.
destruct X3 as [X3|X3]; SimpS.
- Apply step_obs_sf in X4. SimpS.
  left. split. easy. 
  destruct (beq_buset_t o y); Inverts H2;
  constructor; easy.
- Apply step_obs_sf in X4. SimpS.
  case_eq (beq_buset_t y o); intro E.
  + rewrite E in H2; Inverts H2.
    apply beq_buset_imp_eq in E. subst.
    right. split. easy. constructor; easy.
  + rewrite E in H2; Inverts H2.
    left. split. easy. constructor. 
    apply dtr1_r_imp_d'r. easy.
Qed. 

Lemma step_Dtr0_rr' : forall S T (i s:{|S|}) (o o':{|T|}) (c c' c'':circuit S T) (cc cc':circuit S (T#(T#T))) t t3, 
                       pure_bset {i,o,o',s} 
                    -> Dtr0_rr' (ibs0 i) (obs0 o o') c c' cc 
                    -> step c' s t c''
                    -> step cc s t3 cc' 
                    -> t3={o,{o,o'}} /\ Dtr1_rr' (ibs1 s i) (obs1 t o) c c' c'' cc'.
Proof.
introv P D H1 H2. SimpS.
Inverts D. Apply invstepDTRc in H2.
destruct H2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X1[X2[X3[X4[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS. Apply step0_tcbv in X2. SimpS.
Apply step_ibs in X1; try apply pure_buildBus. SimpS.
Apply step0_mb_rr' with H1 H14 in X3. SimpS.
Apply step0_obs_sbf in X4; try apply pure_buildBus. SimpS.
split. easy. constructor. easy.
Qed. 


Lemma step_Dtr1_d : forall S T (i s:{|S|}) (o o' x y:{|T|}) (c c' c'':circuit S T) (cc cc':circuit S (T#(T#T))) t3, 
                      pure_bset {s,i,o,o',x,y}
                    -> Dtr1_d (ibs1 s i) (dtrOB_T x o' y o' o') c c' c'' cc -> step c' s o c''
                    -> step cc s t3 cc' 
                    -> t3={o',{o',o'}} /\ Dtr0_d' (ibs0 s) (dtrOB_T o x o y o')  c' c'' cc'.
Proof. 
introv P D H1 H2. SimpS.
Inverts D. Apply invstepDTRc in H2.
destruct H2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X1[X2[X3[X4[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS. Apply step1_tcbv in X2. SimpS.
Apply step_ibs in X1; try apply pure_buildBus. SimpS.
Apply step1_mb_d with H1 H18 in X3. SimpS.
Apply step_obs_sf in X4; try apply pure_buildBus. SimpS. 
split. easy. constructor. easy.
Qed.


Lemma step_Dtr1_rr' : forall S T (i s:{|S|}) (o o':{|T|}) (c c' c'':circuit S T) (cc cc':circuit S (T#(T#T))) t3, 
                       pure_bset {s,i,o,o'}
                    -> Dtr1_rr' (ibs1 s i) (obs1 o o') c c' c'' cc -> step c' s o c''
                    -> step cc s t3 cc' 
                    -> t3={o',{o',o'}} /\ Dtr0_r' (ibs0 s) (obs0 o o') c' c'' cc'.
Proof. 
introv P D H1 H2.  SimpS.
Inverts D. Apply invstepDTRc in H2.
destruct H2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X1[X2[X3[X4[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS. Apply step1_tcbv in X2. SimpS.
Apply step_ibs in X1; try apply pure_buildBus. SimpS.
Apply step1_mb_rr' with H1 H16 in X3. SimpS.
Apply step1_obs_sbf in X4; try apply pure_buildBus. 
SimpS. split. easy. constructor. easy.
Qed.


Lemma step_Dtr1_r : forall S T (i s:{|S|}) (o o' z:{|T|}) (c c' c'':circuit S T) (cc cc':circuit S (T#(T#T))) t3, 
                       pure_bset {s,i,o,o',z}
                    -> Dtr1_r (ibs1 s i) (dtrOB_T o z o o' o') c c' c'' cc -> step c' s o c''
                    -> step cc s t3 cc' 
                    -> t3={z,{o',o'}} /\ Dtr0_r' (ibs0 s) (obs0 o o') c' c'' cc'.
Proof.
introv P D H1 H2. SimpS.
Inverts D. Apply invstepDTRc in H2.
destruct H2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X1[X2[X3[X4[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS. Apply step1_tcbv in X2. SimpS.
Apply step_ibs in X1; try apply pure_buildBus. SimpS.
Apply step1_mb_r with H1 H17 in X3. SimpS.
Apply step_obs_sf in X4; try apply pure_buildBus. 
SimpS. split. easy. constructor. easy.
Qed. 


Lemma step_Dtr0_r  : forall S T (i s:{|S|}) (o o':{|T|}) (c c' c'':circuit S T) (cc cc':circuit S (T#(T#T))) t t3, 
                      pure_bset {s,i,o,o'}
                   -> Dtr0_r (ibs0 i) (obs0 o o') c c' cc 
                   -> step c' s t c''
                   -> step cc s t3 cc' 
                   -> t3={o,{o,o'}} /\ Dtr1_r (ibs1 s i) (obs1 t o) c c' c'' cc'.
Proof. 
introv P D H1 H2. SimpS.
Inverts D. Apply invstepDTRc in H2.
destruct H2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X1[X2[X3[X4[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS. Apply step0_tcbv in X2. SimpS.
Apply step_ibs in X1; try apply pure_buildBus. SimpS.
Apply step0_mb_r with H1 H14 in X3. SimpS.
Apply step0_obs_sbf in X4; try apply pure_buildBus. 
SimpS. split. easy. constructor. easy. 
Qed. 


Lemma step_Dtr0_r' : forall S T (i s:{|S|}) (o o':{|T|}) (c c' c'':circuit S T) (cc cc':circuit S (T#(T#T))) t t3, 
                      pure_bset {s,i,o,o'}
                   -> Dtr0_r' (ibs0 i) (obs0 o o') c c' cc -> step c' s t c''
                   -> step cc s t3 cc' 
                   -> t3={o,{o,o'}} /\ Dtr1_r' (ibs1 s i) (obs1 t o) c c' c'' cc'.
Proof. 
introv P D H1 H2. SimpS.
Inverts D. Apply invstepDTRc in H2.
destruct H2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X1[X2[X3[X4[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS. Apply step0_tcbv in X2. SimpS.
Apply step_ibs in X1; try apply pure_buildBus. SimpS.
Apply step0_mb_r' with H1 H14 in X3. SimpS.
Apply step0_obs_sbf in X4; try apply pure_buildBus. 
SimpS. split. easy. constructor. easy. 
Qed. 
  
Lemma step_Dtr1_r' : forall S T (i s:{|S|}) (o o':{|T|}) (c c' c'':circuit S T) (cc cc':circuit S (T#(T#T))) t3, 
                      pure_bset {s,i,o,o'}
                   -> Dtr1_r' (ibs1 s i) (obs1 o o') c c' c'' cc -> step c' s o c''
                   -> step cc s t3 cc' 
                   -> t3={o',{o',o'}} /\ Dtrs0 (ibs0 s) (obs0 o o') c' c'' cc'.
Proof. 
introv P D H1 H2. SimpS.
Inverts D. Apply invstepDTRc in H2.
destruct H2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X1[X2[X3[X4[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS. Apply step1_tcbv in X2. SimpS.
Apply step_ibs in X1; try apply pure_buildBus. SimpS.
Apply step1_mb_r' with H1 H16 in X3. SimpS.
Apply step1_obs_sbf in X4; try apply pure_buildBus. 
SimpS. split. easy. constructor. easy.
Qed. 

(* to be placed in relationProp.v 

Lemma dtrec_rr'_imp_d'rr' : forall S T (c c':circuit S T) c2, 
                          dtrec_rr' c c' c2 -> dtrec_d'rr' c c' c2.
Proof.
introv H. induction H; try (constructor; easy).
Inverts H; repeat constructor; try easy; 
try Inverts IHdtr0; try Inverts H0; try constructor; eauto. 
Qed.*)


Lemma step_Dtr1_d'rf : forall S T (i0 i1:{|S|}) (o0 o1 z1 z2:{|T|}) (c0 c1 c2:circuit S T) 
                                   (cc cc':circuit S (T#(T#T))) t3, 
                        pure_bset {i0,i1,o0,o1,z1,z2}
                     -> Dtr1_d'rf (ibs1 i1 i0) (dtrOB_T o1 z1 o1 z2 o0) c0 c1 c2 cc 
                     -> step c0 i0 o0 c1 -> step c1 i1 o1 c2
                     -> step cc i1 t3 cc' 
                     -> t3={o0,{o0,o0}} /\ Dtr2_d'rr' (ibs0 i1) (dtrOB_T o0 o1 o0 o1 z2) c2 c1 cc'.
Proof. 
introv P D X1 X2 X3. SimpS.
Inverts D. Apply invstepDTRc in X3.
destruct X3 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X[X4[X5[X6[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS.
Apply stepr1_tcbv in X4. SimpS.
Apply step12_ibs in X; try apply pure_buildBus. SimpS.
Apply step1_mb_d'r with X1 H16 in X5. SimpS.
Apply stepr1_obs in X6. SimpS.
split. easy. constructor.
eapply dtrec_rr'_imp_d'rr'. easy.
Qed.



(* new version - ???? *)
Lemma step_Dtr1_df : forall S T (i0 i1:{|S|}) (o0 o1 x y z:{|T|}) (c0 c1 c2:circuit S T) 
                                 (cc cc':circuit S (T#(T#T))) t3, 
                         pure_bset {i0,i1,o0,x,y,z}
                     -> Dtr1_df (ibs1 i1 i0) (dtrOB_T x o0 y o0 z) c0 c1 c2 cc 
                     -> step c0 i0 o0 c1 -> step c1 i1 o1 c2
                     -> step cc i1 t3 cc' 
                     -> t3={o0,{o0,o0}} /\ Dtr2_d'rr' (ibs0 i1) (dtrOB_T o0 x o0 y o0) c2 c1 cc'.
Proof. 
introv P D X1 X2 X3. SimpS.
Inverts D. Apply invstepDTRc in X3.
destruct X3 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X[X4[X5[X6[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS.
Apply stepr1_tcbv in X4. SimpS.
Apply step12_ibs in X; try apply pure_buildBus. SimpS.
Apply step1_mb_dF with X1 H16 in X5. SimpS.
Apply stepr1_obs in X6. SimpS.
split. easy. constructor. easy.
Qed. 

Lemma step_Dtr2_d'rr' : forall S T (i1 i2:{|S|}) (o0 o1 o2 z:{|T|}) (c1 c2 c3:circuit S T) 
                                 (cc cc':circuit S (T#(T#T))) t3, 
                         pure_bset {i1,i2,o0,o1,o2,z}
                      -> Dtr2_d'rr' (ibs0 i1) (dtrOB_T o0 o1 o0 o1 z) c2 c1 cc
                      -> step c1 i1 o1 c2 -> step c2 i2 o2 c3 
                      -> step cc i2 t3 cc' 
                      -> t3={o0,{o0,o0}} 
                      /\ Dtr3_d'rr' (ibs1 i2 i1) (dtrOB_T o1 o0 o1 o0 o1) c1 c2 cc'.
Proof.  
introv P D X1 X2 X3. SimpS.
Inverts D. Apply invstepDTRc in X3.
destruct X3 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X[X4[X5[X6[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS.
Apply stepr2_tcbv in X4. SimpS.
Apply step12_ibs in X; try apply pure_buildBus. SimpS.
Apply stepr2_mb_d'rr' with X1 H16 in X5. SimpS.
Apply stepr23_obs in X6. SimpS.
split. easy. constructor. easy.
Qed.

(* generalizes the previous. remove the previous ?? *)
Lemma step_Dtr2_d'rr'' : forall S T (i1 i2:{|S|}) (o0 o1 o2 x:{|T|}) (c1 c2 c3:circuit S T) 
                                 (cc cc':circuit S (T#(T#T))) t3, 
                        pure_bset {i1,i2,o0,o1,o2,x}
                     -> Dtr2_d'rr' (ibs0 i1) (dtrOB_T o0 x o0 x o0) c2 c1 cc
                     -> step c1 i1 o1 c2 -> step c2 i2 o2 c3 
                     -> step cc i2 t3 cc' 
                     -> t3={o0,{o0,o0}} 
                     /\ Dtr3_d'rr' (ibs1 i2 i1) (dtrOB_T o1 o0 o1 o0 x) c1 c2 cc'.
Proof. 
introv P D X1 X2 X3. SimpS.
Inverts D. Apply invstepDTRc in X3.
destruct X3 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X[X4[X5[X6[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS.
Apply stepr2_tcbv in X4. SimpS.
Apply step12_ibs in X; try apply pure_buildBus. SimpS.
Apply stepr2_mb_d'rr' with X1 H16 in X5. SimpS.
Apply stepr23_obs in X6. SimpS.
split. easy. constructor. easy.
Qed.


Lemma step_Dtr3_d'rr' : forall S T (i1 i2:{|S|}) (o0 o1 o2:{|T|}) (c1 c2 c3:circuit S T) 
                                 (cc cc':circuit S (T#(T#T))) t3, 
                        pure_bset {i1,i2,o0,o1,o2}
                     -> Dtr3_d'rr' (ibs1 i2 i1) (dtrOB_T  o1 o0 o1 o0 o1) c1 c2 cc
                     -> step c2 i2 o2 c3 
                     -> step cc i2 t3 cc' 
                     -> t3={o1,{o1,o1}} 
                     /\ Dtr4_d'rr' (ibs0 i2) (dtrOB_T o2 o1 o2 o1 o0) c2 c3 cc'.
Proof.
introv P D X1 X2. SimpS.
Inverts D. Apply invstepDTRc in X2.
destruct X2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X[X4[X5[X6[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS.
Apply stepr3_tcbv in X4. SimpS.
Apply step_ibs in X; try apply pure_buildBus. SimpS.
replace {~ 0, ~ 1, ~ 0} with {~ 0, ~ 1, bool2bset false} in X5. 2: easy.
Apply stepr3_mb_d'rr' with X1 H13 in X5. SimpS.
Apply stepr23_obs in X6. SimpS.
split. easy. constructor. easy.
Qed.

Lemma step_Dtr3_d'rr'' : forall S T (i1 i2:{|S|}) (o0 o1 o2 x:{|T|}) (c1 c2 c3:circuit S T) 
                                 (cc cc':circuit S (T#(T#T))) t3, 
                        pure_bset {i1,i2,o0,o1,o2,x}
                     -> Dtr3_d'rr' (ibs1 i2 i1) (dtrOB_T  o1 o0 o1 o0 x) c1 c2 cc
                     -> step c2 i2 o2 c3 
                     -> step cc i2 t3 cc' 
                     -> t3={o1,{o1,o1}} 
                     /\ Dtr4_d'rr' (ibs0 i2) (dtrOB_T o2 o1 o2 o1 o0) c2 c3 cc'.
Proof. 
introv P D X1 X2. SimpS.
Inverts D. Apply invstepDTRc in X2.
destruct X2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X[X4[X5[X6[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS.
Apply stepr3_tcbv in X4. SimpS.
Apply step_ibs in X; try apply pure_buildBus. SimpS.
replace {~ 0, ~ 1, ~ 0} with {~ 0, ~ 1, bool2bset false} in X5. 2: easy.
Apply stepr3_mb_d'rr' with X1 H14 in X5. SimpS.
Apply stepr23_obs in X6. SimpS.
split. easy. constructor. easy.
Qed.

Lemma step_Dtr4_d'rr' : forall S T (i2 i3:{|S|}) (o0 o1 o2 o3:{|T|}) (c2 c3 c4:circuit S T) 
                                  (cc cc':circuit S (T#(T#T))) t3, 
                        pure_bset {i2,i3,o0,o1,o2,o3}
                     -> Dtr4_d'rr' (ibs0 i2) (dtrOB_T o2 o1 o2 o1 o0) c2 c3 cc
                     -> step c3 i3 o3 c4 
                     -> step cc i3 t3 cc' 
                     -> t3={o1,{o1,o0}} 
                     /\ Dtr5_rr' (ibs1 i3 i2) (dtrOB_T o3 o2 o3 o2 o1) c3 c4 cc'.
Proof.  
introv P D X1 X2. SimpS.
Inverts D. Apply invstepDTRc in X2.
destruct X2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X[X4[X5[X6[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS.
Apply stepr4_tcbv in X4. SimpS.
Apply step_ibs in X; try apply pure_buildBus. SimpS.
replace {~ 0, ~ 1, ~ 0} with {~ 0, ~ 1, bool2bset false} in X5. 2: easy.
Apply stepr4_mb_d'rr' with X1 H14 in X5. SimpS.
Apply stepr4_obs in X6. SimpS.
split. easy. constructor. easy.
Qed.

Lemma step_Dtr5_d'rr' : forall S T (i2 i3:{|S|}) (o1 o2 o3:{|T|}) (c3 c4:circuit S T) 
                                 (cc cc':circuit S (T#(T#T))) t3, 
                        pure_bset {i2,i3,o1,o2,o3}
                     -> Dtr5_rr' (ibs1 i3 i2) (dtrOB_T o3 o2 o3 o2 o1) c3 c4 cc
                     -> step c3 i3 o3 c4 
                     -> step cc i3 t3 cc' 
                     -> t3={o2,{o2,o1}} 
                     /\ Dtr0_r' (ibs0 i3) (dtrOB_T o3 o3 o3 o3 o2) c3 c4 cc'.
Proof.  
introv P D X1 X2. SimpS.
Inverts D. Apply invstepDTRc in X2.
destruct X2 as [?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[?[X[X4[X5[X6[?[?[? ?]]]]]]]]]]]]]]]]]]]]]]]]]].
SimpS.
Apply stepr5_tcbv in X4. SimpS.
Apply step_ibs in X; try apply pure_buildBus. SimpS.
replace {~1, ~ 0, ~ 0} with {~ 1, ~ 0, bool2bset false} in X5. 2: easy.
Apply stepr5_mb_rr' with H13 X1 in X5. SimpS.
Apply stepr5_obs in X6. SimpS. 
split. easy. subst. constructor. easy.
Qed.
