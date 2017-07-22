(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The triple modular redundancy transformation   
#</h1>#    
-   Lemmas about step normal execution and error propagation

              Pascal Fradet - Inria - 2014  
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\Common\".

Require Export ttrInv.

Set Implicit Arguments.


(** Basic properties of evaluation of TTR circuits without faults  *)

Ltac Redstep_G := repeat ((eapply Sseq || eapply Spar ||eapply Sloop || constructor); simpl).

Lemma step_ttrs0 : forall S T (c c' c'':circuit S T) (c3:circuit (S # (§ # §)) (T # (§ # §))) s t, 
                   pure_bset s -> ttrs0 c c' c3 
                -> step c' s t c''
                -> exists c3', step c3 {s,{~1,~1}} {t,{~1,~1}} c3' /\ ttrs1 c' c'' c3'.
Proof. 
introv P R H.
induction H.
- exists c3. Inverts R. split; RedstepG.
- exists c3. Inverts R. split; RedstepG.
- Inverts R. 
  Apply IHstep1 in H6. 
  destruct H6 as [c31' [? ?]]. Purestep H1. SimpS.
  Apply IHstep2 in H9.  
  destruct H9 as [c32' [? ?]].
  exists (c31'-o-c32'). split; RedstepG. 
- Inverts R. Simpl. 
  Apply IHstep1 in H4. 
  Apply IHstep2 in H10. SimpS.
  exists ((SWAP_LR S U (§ # §))-o--|x0,ID|--o-(SWAP_LS T (§ # §) U)-o--| ID, x|--o-RSH).
  split; RedstepG.
- Inverts R. Inverts H8.
  Apply IHstep in H7. SimpS.
  exists (-{b'}-((SWAP_LS S (§#§) §) -o- -|ID ,mb_ttr d3 d3 d3 d3|- -o- RSH
                                 -o- x -o- (SWAP_LR T § (§#§)))).
  split.
  + Redstep_G; destruct d3; try exact H; try exact H1; try easy.
  + repeat constructor; easy.
Qed.


Lemma step_ttrs1 : forall S T (c c':circuit S T) (c3:circuit (S # (§ # §)) (T # (§ # §))) s t, 
                   pure_bset s  -> ttrs1 c c' c3 
                -> step c s t c'
                -> exists c3', step c3 {s,{~0,~0}} {t,{~0,~0}} c3' /\ ttrs2 c c' c3'.
Proof. 
introv P R H.
induction H.
- exists c3. Inverts R. split; RedstepG.
- exists c3. Inverts R. split; RedstepG.
- Inverts R. Simpl. 
  Apply IHstep1 in H5. 
  destruct H5 as [c31' [? ?]].
  Apply IHstep2 in H10.  
  destruct H10 as [c32' [? ?]].
  exists (c31'-o-c32'). split; RedstepG.  
- Inverts R. Simpl. 
  Apply IHstep1 in H4. 
  Apply IHstep2 in H11.
  SimpS.
  exists ((SWAP_LR S U (§ # §))-o--|x0,ID|--o-(SWAP_LS T (§ # §) U)-o--| ID, x|--o-RSH).
  split; RedstepG.
- Inverts R. Inverts H9.
  Apply IHstep in H6. SimpS.
  exists (-{d1}-((SWAP_LS S (§#§) §) -o- -|ID ,mb_ttr d1 kB kB kB|- -o- RSH
                                 -o- x -o- (SWAP_LR T § (§#§)))).
  split.
  + Redstep_G; destruct kB; try exact H; try exact H1; try apply fact_s2bob2s; easy.
  + repeat constructor; easy.
Qed.

Lemma step_ttrs2 : forall S T (c c':circuit S T) (c3:circuit (S # (§ # §)) (T # (§ # §))) s t, 
                   pure_bset s  -> ttrs2 c c' c3 
                -> step c s t c'
                -> exists c3', step c3 {s,{~0,~0}} {t,{~0,~0}} c3' /\ ttrs0 c c' c3'.
Proof. 
introv P R H.
induction H.
- exists c3. Inverts R. split; RedstepG.
- exists c3. Inverts R. split; RedstepG.
- Inverts R. Simpl. 
  Apply IHstep1 in H5.
  destruct H5 as [c31' [? ?]].
  Apply IHstep2 in H10.  
  destruct H10 as [c32' [? ?]].
  exists (c31'-o-c32'). split; RedstepG. 
- Inverts R. Simpl. 
  Apply IHstep1 in H4. 
  Apply IHstep2 in H11.
  SimpS. 
  exists ((SWAP_LR S U (§ # §))-o--|x0,ID|--o-(SWAP_LS T (§ # §) U)-o--| ID, x|--o-RSH).
  split; RedstepG.
- Inverts R. Inverts H9.
  Apply IHstep in H6. SimpS.
  exists (-{d2}-((SWAP_LS S (§#§) §) -o- -|ID ,mb_ttr d2 d2 kB kB|- -o- RSH
                                 -o- x -o- (SWAP_LR T § (§#§)))).
  split.
  + Redstep_G; destruct kB; try exact H; try exact H1; try apply fact_s2bob2s; easy.
  + repeat constructor; easy.
Qed.

(** Similar lemmas expressed differently *)

Lemma ttrs0_step : forall S T (c c' c'':circuit S T) (c3 c3':circuit (S # (§ # §)) (T # (§ # §))) s t t', 
                   pure_bset s -> ttrs0 c c' c3 
                -> step c' s t c''
                -> step c3 {s,{~1,~1}} t' c3'
                -> t'= {t,{~1,~1}} /\ ttrs1 c' c'' c3'.
Proof.
introv P R G H.
induction c'; Inverts R; Inverts G.
- Invstep H; Simpl. 
- Invstep H; Simpl.
- Inverts H. Rpure. 
  Apply IHc'1 with H4 H6 in H5. SimpS.
  Apply IHc'2 with H11 H13 in H8.
  Simpl. 
- Dd_buset t'.
  apply invstepTTRpar in H.
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]].
  SimpS.  
  Apply IHc'1 with H4 G2 in H3. SimpS.
  Apply IHc'2 with G3 H12 in H9.
  split; Simpl. constructor; easy.
- Dd_buset t'. Simpl.
  apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H7. apply step0_mb_ttr2 in G4. SimpS.
  Apply IHc' with H6 H10 in G3.
  Simpl. split; try easy. repeat constructor. easy.
Qed.


Lemma ttrs1_step : forall S T (c c':circuit S T) (c3 c3':circuit (S # (§ # §)) (T # (§ # §))) s t t', 
                   pure_bset s  -> ttrs1 c c' c3 
                -> step c s t c'
                -> step c3 {s,{~0,~0}} t' c3' 
                -> t'={t,{~0,~0}} /\ ttrs2 c c' c3'.
Proof.
introv P R G H.
induction c; Inverts R; Inverts G.
- Invstep H; Simpl. 
- Invstep H; Simpl.
- Inverts H. Rpure. 
  Apply IHc1 with H4 H6 in H5. SimpS.
  Apply IHc2 with H12 H13 in H8. Simpl. 
- Dd_buset t'.
  apply invstepTTRpar in H.
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]]. SimpS.
  Apply IHc1 with G2 H4 in H3. SimpS.
  Apply IHc2 with G3 H13 in H9.
  split; Simpl. constructor; easy.
- Dd_buset t'. Simpl.
  apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H7. apply step1_mb_ttr1 in G4. SimpS.
  Apply IHc with H6 H11 in G3.
  Simpl. split; try easy. repeat constructor. easy.
Qed.

Lemma ttrs2_step : forall S T (c c':circuit S T) (c3 c3':circuit (S # (§ # §)) (T # (§ # §))) s t t', 
                   pure_bset s  
                -> ttrs2 c c' c3 
                -> step c s t c'
                -> step c3 {s,{~0,~0}} t' c3' 
                -> t'={t,{~0,~0}} /\ ttrs0 c c' c3'.
Proof.
introv P R G H.
induction c; Inverts R; Inverts G.
- Invstep H; Simpl. 
- Invstep H; Simpl.
- Inverts H. Rpure. 
  Apply IHc1 with H4 H6 in H5. SimpS.
  Apply IHc2 with H12 H13 in H8. Simpl. 
- Dd_buset t'.
  apply invstepTTRpar in H. 
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]]. SimpS. 
  Apply IHc1 with G2 H4 in H3. SimpS.
  Apply IHc2 with G3 H13 in H9.
  split; Simpl. constructor; easy.
- Dd_buset t'. Simpl.
  apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H7. apply step1_mb_ttr1 in G4. SimpS.
  Apply IHc with H6 H11 in G3.
  Simpl. split; try easy. repeat constructor. easy.
Qed.

(** Reduction with one of the signals {s,{fA,fB}} corrupted *)

Lemma ttrs0_step_fA : forall S T (x c c':circuit S T) (c3 c3':circuit (S#(§#§)) (T#(§#§))) s t t3 fA, 
                      pure_bset s 
                   -> ttrs0 x c c3 
                   -> step c s t c' 
                   -> step c3 {s,{fA,~1}} t3 c3'
                   -> t3={t,{fA,~1}} /\ ttrs1 c c' c3'.
Proof. 
introv P R H G.
induction H; Inverts R.
- Invstep G. Simpl.
- Invstep G. Simpl.
- Inverts G. Simpl.
  eapply IHstep1 with (x:=c5) in H5; try exact H6; try easy. SimpS. 
  apply IHstep2 with (x:=c6) in H12; try easy. Simpl.  
- Dd_buset t3.
  apply invstepTTRpar in G.
  destruct G as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]]. SimpS.
  Apply IHstep1 with H4 in G2. SimpS.
  Apply IHstep2 with H10 in G3. SimpS.
  split. easy. constructor; easy.
- Dd_buset t3.
  apply invstepTTRloop in G.
  destruct G as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H8. apply step0_mb_ttr4 in G4. SimpS.
  Apply IHstep with H7 in G3.  
  Simpl. split. easy. repeat constructor. easy.
Qed.

Lemma ttrs0_step_fB : forall S T (x c c':circuit S T) (c3 c3':circuit (S#(§#§)) (T#(§#§))) s t t3 fB, 
                      pure_bset s 
                   -> ttrs0 x c c3 
                   -> step c s t c'
                   -> step c3 {s,{~1,fB}} t3 c3'
                   -> t3 = {t,{~1,fB}} /\ ttrs1 c c' c3'.
Proof. 
introv P R H G.
induction H; Inverts R.
- Invstep G. Simpl.
- Invstep G. Simpl.
- Inverts G. Simpl.
  eapply IHstep1 with (x:=c5) in H5; try exact H6; try easy. SimpS. 
  apply IHstep2 with (x:=c6) in H12; try easy. Simpl.  
- Dd_buset t3.
  apply invstepTTRpar in G.
  destruct G as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]]. SimpS.
  Apply IHstep1 with H4 in G2. SimpS.
  Apply IHstep2 with H10 in G3. Simpl.
  split. easy. constructor; easy.
- Dd_buset t3.
  apply invstepTTRloop in G.
  destruct G as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H8. apply step0_mb_ttr5 in G4. Simpl.
  Apply IHstep with H7 in G3.  
  Simpl. split. easy. repeat constructor. easy.
Qed.

Lemma ttrs0_step_s : forall S T (x c c':circuit S T) (c3 c3':circuit (S#(§#§)) (T#(§#§))) s s' t t3, 
                      ttrs0 x c c3 
                   -> step c s t c'
                   -> step c3 {s',{~1,~1}} t3 c3'
                   -> sndS t3 = {~1,~1} /\ ttrg1_d1 c c' c3'.
Proof.
introv R H G.
induction H; Inverts R.
- Invstep G. Simpl.
- Invstep G. Simpl.
- Inverts G. SimpS.
  eapply IHstep1 with (x:=c5) in H5; try exact H6; try easy. SimpS. 
  apply IHstep2 with (x:=c6) in H12; try easy. Simpl.  
- Dd_buset t3.
  apply invstepTTRpar in G. 
  destruct G as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]]. SimpS.
  Apply IHstep1 with H4 in G2. SimpS.
  Apply IHstep2 with H10 in G3. Simpl.
  split. easy. constructor; easy.
- Dd_buset t3.
  apply invstepTTRloop in G. destruct G as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H8. apply step0_mb_ttr4 in G4. SimpS.
  Apply IHstep with H7 in G3.  
  Simpl. split. easy. repeat constructor. easy.
Qed.


(** For steps 3i-1 *)
Lemma ttrs1_step_fA : forall S T (c c':circuit S T) (c3 c3':circuit (S#(§#§)) (T#(§#§))) s t t3 fA, 
                      pure_bset s 
                   -> ttrs1 c c' c3 
                   -> step c s t c' 
                   -> step c3 {s,{fA,~0}} t3 c3'
                   -> t3={t,{fA,~0}} /\ ttrs2 c c' c3'.
Proof. 
introv P R H G.
induction H; Inverts R.
- Invstep G. Simpl.
- Invstep G. Simpl.
- Inverts G. Simpl.
  Apply IHstep1 with H6 in H5. SimpS. 
  Apply IHstep2 with H12 in H10. Simpl.  
- Dd_buset t3.
  apply invstepTTRpar in G. 
  destruct G as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]]. SimpS.
  Apply IHstep1 with H4 in G2. SimpS.
  Apply IHstep2 in G3. SimpS.
  split. easy. constructor; easy.
- Dd_buset t3.
  apply invstepTTRloop in G.
  destruct G as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H9. apply step1_mb_ttr4 in G4. SimpS.
  Apply IHstep in G3.  
  Simpl. split. easy. repeat constructor. easy.
Qed.

Lemma ttrs1_step_fB : forall S T (c c':circuit S T) (c3 c3':circuit (S#(§#§)) (T#(§#§))) s t t3 fB, 
                      pure_bset s 
                   -> ttrs1 c c' c3 
                   -> step c s t c' 
                   -> step c3 {s,{~0,fB}} t3 c3'
                   -> t3={t,{~0,fB}} /\ ttrs2 c c' c3'.
Proof.
introv P R H G.
induction H; Inverts R.
- Invstep G. Simpl.
- Invstep G. Simpl.
- Inverts G. Simpl.
  Apply IHstep1 with H6 in H5. SimpS. 
  Apply IHstep2 with H12 in H10. Simpl.  
- Dd_buset t3.
  apply invstepTTRpar in G. 
  destruct G as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]]. SimpS.
  Apply IHstep1 with H4 in G2. SimpS.
  Apply IHstep2 in G3. SimpS.
  split. easy. constructor; easy.
- Dd_buset t3.
  apply invstepTTRloop in G.
  destruct G as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H9. apply step1_mb_ttr5 in G4. SimpS.
  Apply IHstep in G3.  
  Simpl. split. easy. repeat constructor. easy.
Qed.


Lemma ttrs1_step_s : forall S T (c c':circuit S T) (c3 c3':circuit (S#(§#§)) (T#(§#§))) s s' t t3, 
                      ttrs1 c c' c3 
                   -> step c s t c'
                   -> step c3 {s',{~0,~0}} t3 c3'
                   -> sndS t3 = {~0,~0} /\ ttrg2_d1 c c' c3'.
Proof.
introv R H G.
induction H; Inverts R.
- Invstep G. Simpl.
- Invstep G. Simpl.
- Inverts G. Simpl.
  Apply IHstep1 with H6 in H5. SimpS. 
  Apply IHstep2 with H12 in H10. Simpl.  
- Dd_buset t3.
  apply invstepTTRpar in G. 
  destruct G as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]]. SimpS.
  Apply IHstep1 with H4 in G2. SimpS.
  Apply IHstep2 in G3. SimpS.
  split. easy. constructor; easy.
- Dd_buset t3.
  apply invstepTTRloop in G.
  destruct G as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H9. apply step1_mb_ttr4 in G4. SimpS.
  Apply IHstep in G3.  
  Simpl. split. easy. repeat constructor. easy.
Qed.

(**            For steps 3i-2                 *)
Lemma ttrs2_step_fA : forall S T (c c':circuit S T) (c3 c3':circuit (S#(§#§)) (T#(§#§))) s t t3 fA, 
                      pure_bset s 
                   -> ttrs2 c c' c3 
                   -> step c s t c' 
                   -> step c3 {s,{fA,~0}} t3 c3'
                   -> t3={t,{fA,~0}} /\ ttrs0 c c' c3'.
Proof. 
introv P R H G.
induction H; Inverts R.
- Invstep G. Simpl.
- Invstep G. Simpl.
- Inverts G. Simpl.
  Apply IHstep1 with H6 in H5. SimpS. 
  Apply IHstep2 with H12 in H10. Simpl.  
- Dd_buset t3.
  apply invstepTTRpar in G. 
  destruct G as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]]. SimpS.
  Apply IHstep1 with H4 in G2. SimpS.
  Apply IHstep2 in G3. SimpS.
  split. easy. constructor; easy.
- Dd_buset t3.
  apply invstepTTRloop in G.
  destruct G as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H9. apply step1_mb_ttr4 in G4. SimpS.
  Apply IHstep in G3.  
  Simpl. split. easy. repeat constructor. easy.
Qed.


Lemma ttrs2_step_fB : forall S T (c c':circuit S T) (c3 c3':circuit (S#(§#§)) (T#(§#§))) s t t3 fB, 
                      pure_bset s 
                   -> ttrs2 c c' c3 
                   -> step c s t c' 
                   -> step c3 {s,{~0,fB}} t3 c3'
                   -> t3={t,{~0,fB}} /\ ttrs0 c c' c3'.
Proof. 
introv P R H G.
induction H; Inverts R.
- Invstep G. Simpl.
- Invstep G. Simpl.
- Inverts G. Simpl.
  Apply IHstep1 with H6 in H5. SimpS. 
  Apply IHstep2 with H12 in H10. Simpl.  
- Dd_buset t3.
  apply invstepTTRpar in G. 
  destruct G as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]]. SimpS.
  Apply IHstep1 with H4 in G2. SimpS.
  Apply IHstep2 in G3. SimpS.
  split. easy. constructor; easy.
- Dd_buset t3.
  apply invstepTTRloop in G.
  destruct G as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H9. apply step1_mb_ttr5 in G4. SimpS.
  Apply IHstep in G3.  
  Simpl. split. easy. repeat constructor. easy.
Qed.


Lemma ttrs2_step_s : forall S T (c c':circuit S T) (c3 c3':circuit (S#(§#§)) (T#(§#§))) s s' t t3, 
                      ttrs2 c c' c3 
                   -> step c s t c'
                   -> step c3 {s',{~0,~0}} t3 c3'
                   -> sndS t3 = {~0,~0} /\ ttrg0_d1 c c' c3'.
Proof.
introv R H G.
induction H; Inverts R.
- Invstep G. Simpl.
- Invstep G. Simpl.
- Inverts G. Simpl.
  Apply IHstep1 with H6 in H5. SimpS. 
  Apply IHstep2 with H12 in H10. Simpl.  
- Dd_buset t3.
  apply invstepTTRpar in G. 
  destruct G as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]]. SimpS.
  Apply IHstep1 with H4 in G2. SimpS.
  Apply IHstep2 in G3. SimpS.
  split. easy. constructor; easy.
- Dd_buset t3.
  apply invstepTTRloop in G.
  destruct G as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H9. apply step1_mb_ttr4 in G4. SimpS.
  Apply IHstep in G3.  
  Simpl. split. easy. repeat constructor. easy.
Qed.


Lemma ttr_step_fAB : forall S T (c c':circuit S T) (c3 c3':circuit (S#(§#§)) (T#(§#§))) smb s t f f', 
                      ttrs smb c c' c3 
                   -> step c3 {s,f} {t,f'} c3'
                   -> f = f'.
Proof.
induction c; introv R H; Inverts R.
- Invstep H. easy.
- Invstep H. easy. 
- Inverts H.
  Dd_buset t0.
  Apply IHc1 with H4 in H5.
  Apply IHc2 with H8 in H11. Simpl.
- Dd_buset s.  Dd_buset t. Dd_buset f.
  apply invstepTTRpar in H. 
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]].
  Apply IHc1 with H3 in G2. SimpS.
  Apply IHc2 with H9 in G3.
- Dd_buset f.
  apply invstepTTRloop in H. 
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  apply fact0_mb_ttr in G4. SimpS. 
  Apply IHc with H6 in G3.
Qed.

(** Basic properties of evaluation of TTR circuits in a corrupted state *)

(** Lemmas decribing the propagation (and removal) of corruption in memory blocks *)
(** For states 3i *)

Lemma step_ttrg0_d2 : forall S T (x c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                      pure_bset s 
                   -> ttrg0_d2 x c c3
                   -> step c s t c'
                   -> step c3 {s, {~1,~1}} t' c3'
                   -> t'={t, {~1,~1}} /\ ttrg1_d3 c c' c3'.
Proof.
introv P F G H.
induction c; Inverts G; Inverts F; Dd_buset t'.
- Invstep H. Simpl.
- Invstep H. Simpl.
- Invstep H. 
  Apply IHc1 with H4 H in H6. Simpl. 
  Apply IHc2 with H9 H0 in H10. Simpl.
- apply invstepTTRpar in H.
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]].
  Inverts P. 
  Apply IHc1 with H3 H4 in G2. SimpS.
  Apply IHc2 with H10 H11 in G3. SimpS.
  split; try easy. constructor; easy.
- apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H9. apply  step0_mb_ttr2 in G4. SimpS. 
  Apply IHc with H6 H8 in G3. Simpl.
  split. easy. repeat constructor. easy.
Qed.

(** En chantier *)

Lemma step_ttrg0_d3 : forall S T (x c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                      pure_bset s 
                   -> ttrg0_d3 x c c3 
                   -> step c s t c' 
                   -> step c3 {s, {~1,~1}} t' c3'
                   -> t'={t, {~1,~1}} /\ ttrs1 c c' c3'.
Proof.
introv P F G H.
induction c; Inverts G; Inverts F; Dd_buset t'.
- Invstep H. Simpl.
- Invstep H. Simpl.
- Invstep H. 
  Apply IHc1 with H4 H in H6. Simpl. 
  Apply IHc2 with H9 H0 in H10. Simpl.
- apply invstepTTRpar in H.
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]].
  Inverts P. 
  Apply IHc1 with H3 H4 in G2. SimpS.
  Apply IHc2 with H10 H11 in G3. SimpS.
  split; try easy. constructor; easy.
- apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H9. apply  step0_mb_ttr3 in G4. SimpS. 
  Apply IHc with H6 H8 in G3. Simpl.
  split. easy. repeat constructor. easy.
Qed.


Lemma step_ttrg0_kB : forall S T (x c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                      pure_bset s 
                   -> ttrg0_kB x c c3 
                   -> step c s t c'
                   -> step c3 {s, {~1,~1}} t' c3'
                   -> t'={t, {~1,~1}} /\ ttrs1 c c' c3'.
Proof.
introv P F G H.
induction c; Inverts G; Inverts F; Dd_buset t'.
- Invstep H. Simpl.
- Invstep H. Simpl.
- Invstep H. 
  Apply IHc1 with H4 H in H6. Simpl. 
  Apply IHc2 with H9 H0 in H10. Simpl.
- apply invstepTTRpar in H.
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]].
  Inverts P. 
  Apply IHc1 with H3 H4 in G2. SimpS.
  Apply IHc2 with H10 H11 in G3. SimpS.
  split; try easy. constructor; easy.
- apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H9. apply  step0_mb_ttr2 in G4. SimpS. 
  Apply IHc with H6 H8 in G3. Simpl.
  split. easy. repeat constructor. easy.
Qed.


Lemma step_ttrg0_d1kA : forall S T (x c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                        pure_bset s 
                     -> ttrg0_d1kA x c c3 
                     -> step c s t c'
                     -> step c3 {s,{~1,~1}} t' c3'
                     -> t'={t,{~1,~1}} /\ ttrg1_d2 c c' c3'.
Proof.
introv P F G H.
induction c; Inverts G; Inverts F; Dd_buset t'.
- Invstep H. Simpl.
- Invstep H. Simpl.
- Invstep H. 
  Apply IHc1 with H4 H in H6. Simpl. 
  Apply IHc2 with H9 H0 in H10. Simpl.
- apply invstepTTRpar in H.
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]].
  Inverts P. 
  Apply IHc1 with H3 H4 in G2. SimpS.
  Apply IHc2 with H10 H11 in G3. SimpS.
  split; try easy. constructor; easy.
- apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H9. apply  step0_mb_ttr1 in G4. SimpS. 
  Apply IHc with H6 H8 in G3. Simpl.
  split. easy. repeat constructor. easy.
Qed.

(** For states 3i-2 *)


Lemma step_ttrg1_d2 : forall S T (c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                      pure_bset s 
                   -> ttrg1_d2 c c' c3 
                   -> step c s t c'
                   -> step c3 {s, {~ 0, ~ 0}} t' c3'
                   -> t'={t, {~ 0, ~ 0}} /\ ttrg2_d3 c c' c3'.
Proof.
introv P F G H.
induction c; Inverts G; Inverts F; Dd_buset t'.
- Invstep H. Simpl.
- Invstep H. Simpl.
- Invstep H. 
  Apply IHc1 with H4 H in H5. Simpl. 
  Apply IHc2 with H9 H0 in H11. Simpl.
- apply invstepTTRpar in H.
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]].
  Inverts P. 
  Apply IHc1 with H3 H4 in G2. SimpS.
  Apply IHc2 with H10 in G3. SimpS.
  split; try easy. constructor; easy.
- apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H10. apply  step1_mb_ttr1 in G4. SimpS. 
  Apply IHc with H8 in G3. Simpl.
  split. easy. repeat constructor. easy.
Qed.

Lemma step_ttrg1_d1kA : forall S T (c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                        pure_bset s 
                     -> ttrg1_d1kA c c' c3 
                     -> step c s t c'
                     -> step c3 {s, {~ 0, ~ 0}} t' c3'
                     -> t'={t, {~ 0, ~ 0}} /\ ttrg2_d2 c c' c3'.
Proof.
introv P F G H.
induction c; Inverts G; Inverts F; Dd_buset t'.
- Invstep H. Simpl.
- Invstep H. Simpl.
- Invstep H. 
  Apply IHc1 with H4 H in H5. Simpl. 
  Apply IHc2 with H9 H0 in H11. Simpl.
- apply invstepTTRpar in H.
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]].
  Inverts P. 
  Apply IHc1 with H3 H4 in G2. SimpS.
  Apply IHc2 with H10 in G3. SimpS.
  split; try easy. constructor; easy.
- apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H10. apply  step2_mb_ttr1 in G4. SimpS. 
  Apply IHc with H8 in G3. Simpl.
  split. easy. repeat constructor. easy.
Qed.


Lemma step_ttrg1_d3 : forall S T (c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                      pure_bset s 
                   -> ttrg1_d3 c c' c3 
                   -> step c s t c'
                   -> step c3 {s, {~ 0, ~ 0}} t' c3'
                   -> t'={t, {~ 0, ~ 0}} /\ ttrs2 c c' c3'.
Proof.
introv P F G H.
induction c; Inverts G; Inverts F; Dd_buset t'.
- Invstep H. Simpl.
- Invstep H. Simpl.
- Invstep H. 
  Apply IHc1 with H4 H in H5. Simpl. 
  Apply IHc2 with H9 H0 in H11. Simpl.
- apply invstepTTRpar in H.
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]].
  Inverts P. 
  Apply IHc1 with H3 H4 in G2. SimpS.
  Apply IHc2 with H10 in G3. SimpS.
  split; try easy. constructor; easy.
- apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H10. apply  step1_mb_ttr1 in G4. SimpS. 
  Apply IHc with H8 in G3. Simpl.
  split. easy. repeat constructor. easy.
Qed.


Lemma step_ttrg1_kB : forall S T (c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                      pure_bset s 
                   -> ttrg1_kB c c' c3 
                   -> step c s t c'
                   -> step c3 {s, {~ 0, ~ 0}} t' c3'
                   -> t'={t, {~ 0, ~ 0}} /\ ttrs2 c c' c3'.
Proof.
introv P F G H.
induction c; Inverts G; Inverts F; Dd_buset t'.
- Invstep H. Simpl.
- Invstep H. Simpl.
- Invstep H. 
  Apply IHc1 with H4 H in H5. Simpl. 
  Apply IHc2 with H9 H0 in H11. Simpl.
- apply invstepTTRpar in H.
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]].
  Inverts P. 
  Apply IHc1 with H3 H4 in G2. SimpS.
  Apply IHc2 with H10 in G3. SimpS.
  split; try easy. constructor; easy.
- apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H10. apply  step1_mb_ttr3 in G4. SimpS. 
  Apply IHc with H8 in G3. Simpl.
  split. easy. repeat constructor. easy.
Qed.


(** For states 3i-1 *)


Lemma step_ttrg2_d1kA : forall S T (c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                        pure_bset s 
                     -> ttrg2_d1kA c c' c3 
                     -> step c s t c'
                     -> step c3 {s, {~ 0, ~ 0}} t' c3'
                     -> t'={t, {~ 0, ~ 0}} /\ ttrg0_d2 c c' c3'.
Proof.
introv P F G H.
induction c; Inverts G; Inverts F; Dd_buset t'.
- Invstep H. Simpl.
- Invstep H. Simpl.
- Invstep H. 
  Apply IHc1 with H4 H in H5. Simpl. 
  Apply IHc2 with H9 H0 in H11. Simpl.
- apply invstepTTRpar in H.
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]].
  Inverts P. 
  Apply IHc1 with H3 H4 in G2. SimpS.
  Apply IHc2 with H10 in G3. SimpS.
  split; try easy. constructor; easy.
- apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H10. apply  step2_mb_ttr1 in G4. SimpS. 
  Apply IHc with H8 in G3. Simpl.
  split. easy. repeat constructor. easy.
Qed.


Lemma step_ttrg2_d2 : forall S T (c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                      pure_bset s 
                   -> ttrg2_d2 c c' c3 
                   -> step c s t c'
                   -> step c3 {s, {~ 0, ~ 0}} t' c3'
                   -> t'={t, {~ 0, ~ 0}} /\ ttrg0_d3 c c' c3'.
Proof.
introv P F G H.
induction c; Inverts G; Inverts F; Dd_buset t'.
- Invstep H. Simpl.
- Invstep H. Simpl.
- Invstep H. 
  Apply IHc1 with H4 H in H5. Simpl. 
  Apply IHc2 with H9 H0 in H11. Simpl.
- apply invstepTTRpar in H.
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]].
  Inverts P. 
  Apply IHc1 with H3 H4 in G2. SimpS.
  Apply IHc2 with H10 in G3. SimpS.
  split; try easy. constructor; easy.
- apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H10. apply  step1_mb_ttr1 in G4. SimpS. 
  Apply IHc with H8 in G3. Simpl.
  split. easy. repeat constructor. easy.
Qed.


Lemma step_ttrg2_d3 : forall S T (c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                      pure_bset s 
                   -> ttrg2_d3 c c' c3 
                   -> step c s t c'
                   -> step c3 {s, {~ 0, ~ 0}} t' c3'
                   -> t'={t, {~ 0, ~ 0}} /\ ttrs0 c c' c3'.
Proof.
introv P F G H.
induction c; Inverts G; Inverts F; Dd_buset t'.
- Invstep H. Simpl.
- Invstep H. Simpl.
- Invstep H. 
  Apply IHc1 with H4 H in H5. Simpl. 
  Apply IHc2 with H9 H0 in H11. Simpl.
- apply invstepTTRpar in H.
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]].
  Inverts P. 
  Apply IHc1 with H3 H4 in G2. SimpS.
  Apply IHc2 with H10 in G3. SimpS.
  split; try easy. constructor; easy.
- apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H10. apply  step1_mb_ttr1 in G4. SimpS. 
  Apply IHc with H8 in G3. Simpl.
  split. easy. repeat constructor. easy.
Qed.


Lemma step_ttrg2_kB : forall S T (c c':circuit S T) (c3 c3': circuit (S#(§#§)) (T#(§#§))) s t t',
                      pure_bset s 
                   -> ttrg2_kB c c' c3 
                   -> step c s t c'
                   -> step c3 {s, {~ 0, ~ 0}} t' c3'
                   -> t'={t, {~ 0, ~ 0}} /\ ttrs0 c c' c3'.
Proof.
introv P F G H.
induction c; Inverts G; Inverts F; Dd_buset t'.
- Invstep H. Simpl.
- Invstep H. Simpl.
- Invstep H. 
  Apply IHc1 with H4 H in H5. Simpl. 
  Apply IHc2 with H9 H0 in H11. Simpl.
- apply invstepTTRpar in H.
  destruct H as [c31'[c32'[y1[y2[G1 [G2 G3]]]]]].
  Inverts P. 
  Apply IHc1 with H3 H4 in G2. SimpS.
  Apply IHc2 with H10 in G3. SimpS.
  split; try easy. constructor; easy.
- apply invstepTTRloop in H.
  destruct H as [c31 [c32 [u1 [u2 [u3 [y [z [G1 [G2 [G3 G4]]]]]]]]]].
  Inverts H10. apply  step1_mb_ttr3 in G4. SimpS. 
  Apply IHc with H8 in G3. Simpl.
  split. easy. repeat constructor. easy.
Qed.


(** General lemmas *)

Lemma step_ttrg0_d2d3kB : forall S T (x c c':circuit S T) 
                                     (c30 c31 c32: circuit (S#(§#§)) (T#(§#§))) s t t1 t2,
                   pure_bset s -> ttrg0_d2d3kB x c c30 -> step c s t c' 
                -> step c30 {s, {~1,~1}} t1 c31
                -> step c31 {s, {~0,~0}} t2 c32
                -> t1={t,{~1,~1}} /\ t2={t,{~0,~0}} /\ ttrs2 c c' c32.
Proof.
introv P1 R H H0 H1. destruct R as [R|[R|R]].
- Apply step_ttrg0_d2 with H H0 in R.
  destruct R as [X1 R].
  Apply step_ttrg1_d3 with H H1 in R.
- Apply step_ttrg0_d3 with H H0 in R.
  destruct R as [X1 R].
  Apply ttrs1_step with H H1 in R.
- Apply step_ttrg0_kB with H H0 in R.
  destruct R as [X1 R].
  Apply ttrs1_step with H H1 in R.
Qed.


Lemma step_ttrg1_d2d3kB : forall S T (c c':circuit S T) 
                                     (c30 c31 c32: circuit (S#(§#§)) (T#(§#§))) s t t1 t2,
                   pure_bset s 
                -> ttrg1_d2d3kB c c' c30 
                -> step c s t c' 
                -> step c30 {s, {~0,~0}} t1 c31
                -> step c31 {s, {~0,~0}} t2 c32
                -> t1={t,{~0,~0}} /\ t2={t,{~0,~0}} /\ ttrs0 c c' c32.
Proof.
introv P1 R H H0 H1. destruct R as [R|[R|R]].
- Apply step_ttrg1_d2 with H H0 in R.
  destruct R as [X1 R].
  Apply step_ttrg2_d3 with H H1 in R.
- Apply step_ttrg1_d3 with H H0 in R.
  destruct R as [X1 R].
  Apply ttrs2_step with H H1 in R.
- Apply step_ttrg1_kB with H H0 in R.
  destruct R as [X1 R].
  Apply ttrs2_step with H H1 in R.
Qed.


Lemma step_ttrg2_d2d3kB : forall S T (c c' c'':circuit S T) 
                                     (c30 c31 c32: circuit (S#(§#§)) (T#(§#§))) s1 s2 t1 t2 t31 t32,
                   pure_bset s1 -> pure_bset s2 
                -> ttrg2_d2d3kB c c' c30 
                -> step c s1 t1 c' 
                -> step c' s2 t2 c'' 
                -> step c30 {s1, {~0,~0}} t31 c31
                -> step c31 {s2, {~1,~1}} t32 c32
                -> t31={t1,{~0,~0}} /\ t32={t2,{~1,~1}} /\ ttrs1 c' c'' c32.
Proof.
introv P1 P2 R H1 H2 H3 H4. destruct R as [R|[R|R]].
- Apply step_ttrg2_d2 with H1 H3 in R.
  destruct R as [X1 R].
  Apply step_ttrg0_d3 with H2 H4 in R.
- Apply step_ttrg2_d3 with H1 H3 in R.
  destruct R as [X1 R].
  Apply ttrs0_step with H2 H4 in R.
- Apply step_ttrg2_kB with H1 H3 in R.
  destruct R as [X1 R].
  Apply ttrs0_step with H2 H4 in R.
Qed.
