(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
- states transitions with a glitch for memoty block
  during even(1) cycles

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)
(* 
Add LoadPath "..\..\Common\".
Require Import CirReflect . 
Add LoadPath "..\..\TMRProof\".
Require Import tmrDef.
Add LoadPath "..\".*)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import dtrTransform relationPred relationProp.
Require Import leftStep leftStepg.
Require Import rightStep memoryInv1 memoryStep rightStepg.

Set Implicit Arguments.

(* ##################################################################### *)
(** Properties of Memory Block with a Glitch during even(1) cycles      *)
(* ##################################################################### *)

(*If the control input fail signal is not restricted and possible glitched,
  fail output is also unknown*)
Lemma step1_mb_f : forall S T (c c' c'':circuit S T) c2 c2' t2 s t f, 
                        pure_bset s -> dtrs1 c c' c'' c2 
                     -> step c' s t c''
                     -> step c2 {s,{~1,~0,f}} t2 c2'
                     -> (exists b,t2 = {t,{~1,~0,b}}) /\ dtrs0 c' c'' c2'.
Proof.
intros S T c. induction c; unfold dtrs0.
- introv P1 R H HT. Inverts R. Invstep HT. Inverts H1. split; Simpl. 
- introv P1 R H HT. Inverts R. Invstep HT. Inverts H1. split; Simpl.
- introv P1 R H HT. Inverts R. Inverts H. Inverts HT. SimpS.
  apply IHc1 with (c':=c1') (c'':= c1'') (t:=t0)  in H3; Simpl. 
  apply IHc2 with (c':=c2'0) (c'':=c2'') (t:=t) in H11; Simpl.
- introv P R H HT. Dd_buset t2. Inverts R. unfold  SWAP_LR in HT. unfold  SWAP_LS in HT.
  Invstep HT. SimpS. Inverts H13.  
  apply IHc1 with  (c2':=x18) (t2:={x9, {x11, x12, x10}}) 
                   (s:=x1) (t:=x) (f:=f)  in H3; try easy. SimpS.
  apply IHc2 with (c3:=c22) (c2':=x40) (t2:={x14, {x16, x17, x15}}) 
                  (s:=x2) (t:=x0) (f:=x3) in H9; try easy. SimpS.
  split; Simpl; constructor; try easy.
- introv P1 R H HT. Dd_buset t2. Inverts R. Inverts H8. unfold memBlock in HT. unfold lhsMB in HT. 
  unfold rhsMB in HT. Invstep HT. SimpS. 
  apply step_rhs in H15. Inverts H20. SimpS. rename x91 into b''. 
  Destruct_s f; destruct x.
   + apply step_lhs with  (sav:=true)(rol:=false) 
                                 (d:= b'') (r:= r) (fai:=false) in H18; try easy. 
      SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1.
      apply IHc with (c':=c'0) (c'':=x3) (t:={t, x75}) in H2; try easy. SimpS. 
      split; Simpl; constructor; try easy. simpl. constructor. Checkpure.
   + apply step_lhs with  (sav:=true) (rol:=false) 
                                 (d:= b'') (r:= r) (fai:=true) in H18; try easy. 
      SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1.
      apply IHc with (c':=c'0) (c'':=x3) (t:={t, x75}) in H2; try easy. SimpS. 
      split; Simpl; constructor; try easy. simpl. constructor. Checkpure.
   + apply step_lhs_f with  (sav:=true) (rol:=false) 
                                 (d:= b'') (r:= r) in H18; try easy. 
      SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1.
      apply IHc with (c':=c'0) (c'':=x3) (t:={t, x75}) in H2; try easy. SimpS. 
      split; Simpl; constructor; try easy. simpl. constructor. Checkpure.
Qed.

(*If the control input save signal is glitched, then save output is also glitched 
  and internal checkpointing mechanism is corrupted *)
Lemma step1_mb_s : forall S T (c c' c'':circuit S T) c2 c2' t2 s t f, 
                        pure_bset s -> pure_bset f-> dtrs1 c c' c'' c2 
                     -> step c' s t c''
                     -> step c2 {s,{~?,~0,f}} t2 c2'
                     -> exists b, t2 = {t,{~?,~0,bool2bset b}} /\ dtr0_rr' c' c'' c2'.
Proof.
intros S T c. induction c.
- introv P1 P2 R H HT. exists (fbset2bool f). Inverts R. Invstep HT. Inverts H1. 
  split. rewrite rew_bool2bsetf; Simpl. repeat constructor.  
- introv P1 P2 R H HT. exists (fbset2bool f). Inverts R. Invstep HT. Inverts H1. 
  split. rewrite rew_bool2bsetf; Simpl. repeat constructor.
- introv P1 P2 R H HT. Inverts R. Inverts H. Inverts HT. SimpS.
  apply IHc1 with (c':=c1') (c'':= c1'') (t:=t0)  in H3; Simpl. 
  apply IHc2 with (c':=c2'0) (c'':=c2'') (t:=t) in H11; Simpl. 
  exists x. split; repeat constructor; easy. Checkpure.
- introv P1 P2 R H HT. Dd_buset t2. Inverts R. unfold  SWAP_LR in HT. unfold  SWAP_LS in HT.
  Inverts H. Invstep HT. SimpS.
  apply IHc1 with  (c':=c1') (c'':= c1'') (t:=t0) in H0; try easy. SimpS.
  eapply IHc2 with (c':=c2'0) (c'':=c2'') (t:=v)  in H9 ; try easy. SimpS.
  exists x0. split; Simpl; constructor; try easy. Checkpure.
- introv P1 P2 R H HT. Dd_buset t2. Inverts R. Inverts H8. unfold memBlock in HT. unfold lhsMB in HT. 
  unfold rhsMB in HT. Inverts H. Invstep HT. SimpS. 
  apply step_rhs in H16. SimpS. 
  apply step_lhs_s with (rol:=false) (d:= d) (r:= r) 
                          (fai:=fbset2bool f) in H19; try easy.
  destruct H19; SimpS. unfold bool2bset in H2. simpl in H2. 
  assert (HX:beq_buset_t (~ ?) (~ ?)= true) by easy. rewrite HX in H1. 
  apply IHc  with (c':=c'0) (c'':=c''0) (t:={t, a}) in H2; try easy. SimpS.
  exists x. split; repeat constructor; try easy. unfold dtr1_rr'; Simpl; 
  destruct H3; Inverts H0; Simpl; repeat constructor; try easy.
  Checkpure. Checkpure. rewrite rew_bool2bsetf; easy.
Qed.

(*If the control input rollback signal is glitched, then d and r cells are corrupted as 
 well as rollback output*)
Lemma step1_mb_b : forall S T (c c' c'':circuit S T) c2 c2' t2 s t x f, 
                      pure_bset f->  dtrs1 c c' c'' c2 
                     -> step c' s t c''
                     -> step c2 {x,{~1,~?,f}} t2 c2'
                     -> (exists x' b, t2 = {x',{~1,~?, bool2bset b}}) /\ dtr0_dr c' c'' c2'.
Proof.
intros S T c. induction c.
- introv P1 R H HT. Inverts R. Invstep HT. Inverts H1. split;Simpl.
  exists (redgate g x) (fbset2bool f). rewrite rew_bool2bsetf; Simpl. repeat constructor.  
- introv P1 R H HT. Inverts R. Invstep HT. Inverts H1. split;Simpl.
  exists (redplug p x) (fbset2bool f). rewrite rew_bool2bsetf; Simpl. repeat constructor.  
- introv P1 R H HT. Inverts R. Inverts H. Inverts HT. SimpS.
  apply IHc1 with (c':=c1') (c'':= c1'') (s:=s) (t:=t0)  in H3; Simpl. 
  apply IHc2 with (c':=c2'0) (c'':=c2'') (s:=t0) (t:=t) in H11; Simpl. 
  split; Simpl. repeat constructor; easy. Checkpure.
- introv P1 R H HT. Dd_buset t2. Inverts R. unfold  SWAP_LR in HT. unfold SWAP_LS in HT.
  Inverts H. Invstep HT. SimpS.
  apply IHc1 with  (c2':=x18) (t2:={x9, {x11, x12, x10}}) 
                   (s:=s0) (t:=t0) (f:=f) (x:=x) in H3; try easy. SimpS.
  apply IHc2 with (c2':=x39) (t2:={x14, {x16, x17, x15}}) 
                  (s:=u) (t:=v) (f:=bool2bset x2) (x:=x0)   in H10 ; try easy. SimpS.
  split; Simpl; constructor; try easy. Checkpure.
- introv P1 R H HT. Dd_buset t2. Inverts R. Inverts H8. unfold memBlock in HT. unfold lhsMB in HT. 
  unfold rhsMB in HT. Inverts H. Invstep HT. SimpS. 
  apply step_rhs in H16. SimpS. 
  apply step_lhs_b with (fai:=fbset2bool f) 
                 (sav:=true)  (d:= d) (r:= r) in H19; try easy.
  destruct H19; SimpS. unfold bool2bset in H2. simpl in H2. 
  simpl in H1. apply IHc  with (c':=c'0) (c'':=c''0) (s:={s, bool2bset r}) (t:={t, a}) in H2;
  try easy. SimpS. split; repeat constructor; try easy. exists x0 x. easy. 
  Checkpure. rewrite rew_bool2bsetf; easy.
Qed.

(*Soft property if input fail signal is pure but not restricted;
it's soft since output data signal is ignored*)
Lemma step1_mb_i : forall S T (c c' c'':circuit S T) c2 c2' t2 s f,
                    pure_bset f->  dtrs1 c c' c'' c2
                   -> step c2 {s,{~1,~0,f}} t2 c2'
                   -> exists t b, t2 = {t,{~1,~0,bool2bset b}} /\ dtr0_dr c' c'' c2'.
Proof.
intros S T c. induction c.
- introv P1 H HT.  Inverts H. Invstep HT. SimpS. 
  exists (redgate g s) (fbset2bool f). rewrite rew_bool2bsetf; Simpl. repeat constructor.  
- introv P1 H HT.  Inverts H. Invstep HT. SimpS. 
  exists (redplug p s) (fbset2bool f). rewrite rew_bool2bsetf; Simpl. repeat constructor.  
- introv P1 H HT. Inverts H. Inverts HT. SimpS.
  apply IHc1 with (c':=c1') (c'':= c1'')  in H3; Simpl. 
  apply IHc2 with (c':=c2'0) (c'':=c2'') in H10; Simpl. 
  exists x  x0. split; Simpl. repeat constructor; easy. Checkpure.
- introv P1 H HT. Dd_buset t2. Inverts H. unfold  SWAP_LR in HT. unfold SWAP_LS in HT.
  Invstep HT. SimpS.
  apply IHc1 with  (c':=c1') (c'':= c1'') in H0; try easy. SimpS.
  apply IHc2 with (c':=c2'0) (c'':=c2'')   in H8 ; try easy. SimpS.
  exists {x1,x3} x4. split; Simpl; constructor; try easy. Checkpure.
- introv P1 H HT. Dd_buset t2. Inverts H. Inverts H8. unfold memBlock in HT. unfold lhsMB in HT. 
  unfold rhsMB in HT. Invstep HT. SimpS. 
  apply step_rhs in H14. SimpS. 
  apply step_lhs  with (d:=d) (r:=r) (sav:=true) (rol:=false) (fai:=fbset2bool f)
  in H17; try easy. destruct H17; SimpS. unfold bool2bset in H2. simpl in H2. 
  simpl in H1. apply IHc  with (c':=c'0) (c'':=c''0)  in H2;
  try easy. SimpS.  exists x0 x. split; repeat constructor; try easy.
  Checkpure. rewrite rew_bool2bsetf; easy.
Qed.

(*If the data input f1 signal is unknown, then d and r cells are corrupted as 
 well as data output and fail output; control wires are {~1,~0, known prossibly glitched} propagates 
 through a memory block*)
Lemma step1_mb_if : forall S T (c c' c'':circuit S T) c2 c2' t2  f1 f2,
                      dtrs1 c c' c'' c2
                   -> step c2 {f1,{~1,~0,f2}} t2 c2'
                   -> (exists e1 e2, t2 = {e1,{~1,~0,e2}}) /\ dtr0_dr c' c'' c2'.
Proof.
intros S T c. induction c.
- introv H HT. Inverts H. Invstep HT.  split;Simpl. constructor.
- introv H HT. Inverts H. Invstep HT.  split;Simpl. constructor. 
- introv H HT. Inverts H. Inverts HT. SimpS.
  apply IHc1 with (c':=c1') (c'':= c1'') in H3; Simpl. 
  apply IHc2 with (c':=c2'0) (c'':=c2'') in H10; Simpl. 
  split; Simpl. repeat constructor; easy.
- introv H HT. Dd_buset t2. Inverts H. unfold  SWAP_LR in HT. unfold SWAP_LS in HT.
  Invstep HT. SimpS.
  apply IHc1 with  (c':=c1') (c'':= c1'') in H0; try easy. SimpS.
  apply IHc2 with (c':=c2'0) (c'':=c2'') in H8 ; try easy. SimpS.
  split; Simpl; constructor; try easy.
- introv H HT. Dd_buset t2. Inverts H. Inverts H8. unfold memBlock in HT. unfold lhsMB in HT. 
  unfold rhsMB in HT. Invstep HT. SimpS. 
  apply step_rhs in H14. SimpS.
  Destruct_s f2; destruct x.
  + apply step_lhs with  (sav:=true) (rol:=false) 
                             (d:= d) (r:= r) (fai:=false) in H17; try easy.
    SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1. 
    apply IHc with (c':=c'0) (c'':=c''0) in H2; try easy. SimpS.
    split. exists x0 x; easy. repeat constructor; try easy.
  + apply step_lhs with  (sav:=true) (rol:=false) (d:= d) (r:= r) (fai:=true) in H17; try easy.
    SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1.
    apply IHc with (c':=c'0) (c'':=c''0) in H2; try easy. SimpS.
    split. exists x0 x; easy. repeat constructor; try easy.
  + apply step_lhs_f with  (sav:=true) (rol:=false) (d:= d) (r:= r) in H17; try easy.
    SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1.
    apply IHc with (c':=c'0) (c'':=c''0) in H2; try easy. SimpS.
    split. exists x0 x; easy. repeat constructor; try easy.
Qed.

(*--------------------------------------- ORIGINAL CORRUPTED STATE ------------------------*)

(**If d' memory cells is possibly corruted during an even cycle
    then d and r both cells become corrupted*)
Lemma step1_mb_id' : forall S T (c c' c'':circuit S T) c2 c2' t2 s t f s',
                     pure_bset s ->  pure_bset s' -> pure_bset f -> dtr1_d'  c c' c'' c2 
                  -> step c' s t c''
                  -> step c2 {s',{~1,~0,f}} t2 c2' 
                  -> (exists t' f, t2 =  {t',{~1,~0,bool2bset f}})
                     /\ dtr0_dr c' c'' c2'. 
Proof. 
intros S T c. induction c.
- introv P1 P2 P3 R H HT. Inverts R. Inverts H. Invstep HT. split; Simpl.
  exists (redgate g s') (fbset2bool f). rewrite rew_bool2bsetf; Simpl. repeat constructor.  
- introv P1 P2 P3 R H HT. Inverts R. Inverts H. Invstep HT. split; Simpl.
  exists (redplug p s') (fbset2bool f). rewrite rew_bool2bsetf; Simpl. repeat constructor.  
- introv P1 P2 P3 R H HT. Inverts R. Inverts H. Inverts HT. SimpS. Rpure.
  apply IHc1 with (c':=c1') (s:=s) (c'':= c1'') (t:=t0)  in H3; Simpl. 
  apply IHc2 with (s':=x5) (c3:=c22) (c2':=c2'1) (t2:= {x1, {x4, x7, x6}}) (f:=bool2bset x8) in H12; Simpl.
  split. exists x x0. easy. repeat constructor; easy.
- introv P1 P2 P3 R H HT. Dd_buset t2. Inverts R. unfold SWAP_LR in HT. unfold  SWAP_LS in HT.
  Invstep HT. SimpS. Inverts H13.  
  apply IHc1 with  (c':=c1') (s:=x3) (c'':= x30) (t:=x1) in H0; try easy. SimpS.
  apply IHc2 with (c3:=c22) (c2':=x40) (t2:={x14, {x16, x17, x15}})
                  (f:=bool2bset x6) (s':=x0)  in H9; try easy. SimpS.
  split; Simpl; constructor; try easy. Checkpure.
- introv P1 P2 P3 R H HT. Dd_buset t2. Inverts R. Inverts H. Inverts H8.
  unfold memBlock in HT. unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS. 
  apply step_rhs in H16. SimpS. Rpure.
  apply step_lhs with  (fai:=fbset2bool f) (sav:=true) 
                             (rol:=false) (d:= d) (r:= r) in H19; try easy. 
  SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1. 
  apply IHc with (c':=c'0) (c'':= c''0) (s:={s, bool2bset r}) (t:={t, a}) in H2; 
  try easy. SimpS. split. exists x0 x; easy. repeat constructor; try easy.
  rewrite rew_bool2bsetf; Simpl.
Qed.

(**if d memory cell is corruted and control signals are (save, rollback, fail)={~1,~0,pure unknown}*)
Lemma step1_mb_d : forall S T (c c' c'':circuit S T) cc cc' t2 s t f,
                     pure_bset s -> pure_bset f -> dtr1_d c c' c'' cc
                  -> step c' s t c''
                  -> step cc {s,{~1,~0,f}} t2 cc'
                  -> (exists f', t2 =  {t,{~1,~0,bool2bset f'}})
                     /\ dtr0_d' c' c'' cc'. 
Proof. 
intros S T c. induction c.
- introv P1 P2 R H HT. Inverts R. Inverts H. Invstep HT. split; Simpl.
  exists (fbset2bool f). rewrite rew_bool2bsetf; Simpl. repeat constructor.  
- introv P1 P2 R H HT. Inverts R. Inverts H. Invstep HT. split; Simpl.
  exists (fbset2bool f). rewrite rew_bool2bsetf; Simpl. repeat constructor.  
- introv P1 P2 R H HT. Inverts R. Inverts H. Inverts HT. SimpS. Rpure.
  apply IHc1 with (c':=c1') (s:=s) (c'':= c1'') (t:=t0)  in H3; Simpl. 
  apply IHc2 with (c':=c2') (c'':=c2'') (t:=t) in H11 ; Simpl.
  split. exists x. easy. repeat constructor; easy.
- introv P1 P2 R H HT. Dd_buset t2. Inverts R. unfold SWAP_LR in HT. unfold  SWAP_LS in HT.
  Invstep HT. SimpS. Inverts H13.  
  apply IHc1 with  (cc':=x18) (t2:={x9, {x11, x12, x10}}) (s:=x1) (t:=x) (f:=f)  in H3; try easy. SimpS.
  apply IHc2 with (cc:=c22) (cc':=x40) (t2:={x14, {x16, x17, x15}}) 
                  (s:=x2) (t:=x0) (f:=bool2bset x3)   in H9; try easy. SimpS.
  split; Simpl; constructor; try easy. Checkpure.
- introv P1 P2 R H HT. Dd_buset t2. Inverts R. Inverts H. Inverts H8.
  unfold memBlock in HT. unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS. 
  apply step_rhs in H16. SimpS. Rpure.
  apply step_lhs with  (fai:=fbset2bool f) (sav:=true) 
                             (rol:=false) (d:= d) (r:= r) in H19; try easy. 
  SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1. 
  apply IHc with (c':=c'0) (c'':= c''0) (s:={s, bool2bset r}) (t:={t, a}) in H2; 
  try easy. SimpS. split. exists x; easy. repeat constructor. easy.
  simpl. Simpl. rewrite rew_bool2bsetf; Simpl.
Qed.

(**if d memory cell is corruted and control signals are (save, rollback, fail)={~1,~1,1}*)
(*it corresponds to the 1st cycle of recovery*)
Lemma step1_mb_dF : forall S T (c c' c'':circuit S T) cc cc' t2 s t, 
                     pure_bset s -> dtr1_d c c' c'' cc
                  -> step c s t c'
                  -> step cc {s,{~1,~1,~1}} t2 cc'
                  -> t2 = {t,{~1,~1,~1}} /\ dtrec_d'rr' c'' c' cc'.
Proof. 
introv P R H HT. induction H.
- Inverts R; split; Invstep HT; Simpl. constructor.
- Inverts R; split; Invstep HT; Simpl. constructor.
- Inverts R. Inverts HT.
  Apply IHstep1 in H6;  Simpl.
  Apply IHstep2 in H12; Simpl. split; Simpl. constructor; easy.
- Inverts R. unfold SWAP_LS in HT. unfold SWAP_LR in HT.
  Invstep HT. SimpS.
  Apply IHstep1 in H0; Simpl.
  Apply IHstep2 in H10; Simpl.
  split; Simpl. constructor; easy.
- Inverts R. unfold memBlock in HT. 
  unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS.
  apply step_rhs in H17. 
  apply step_lhs  with (d:=d) (r:=r)(sav:=true) (rol:=true) (fai:=true) in H20; try easy.
  SimpS. simpl in H1. simpl in H2. 
  assert (HX:(negb (eqb d' d) || true)=true) by (destruct (negb (eqb d' d)); easy). (*[B]*)
  rewrite HX in H2. unfold bool2bset in H2. simpl in H2. Inverts H10.
  apply IHstep with (c'':=c''0) in H2. SimpS.
  split; Simpl; constructor; try easy. constructor. Checkpure. easy.
Qed.

(**if d memory cell is corruted and control signals are (save, rollback, fail)={~1,0,unknown}*)
(*then the next clock cycle, r' becomes corrupted*)
Lemma step1_mb_r : forall S T (c c' c'':circuit S T) c2 c2' t2 s t f,
                     pure_bset s -> dtr1_r c c' c'' c2
                  -> step c' s t c''
                  -> step c2 {s,{~1,~0,f}} t2 c2'
                  -> (exists b, t2 = {t,{~1,~0, b}}) /\ dtr0_r' c' c'' c2'.
Proof.
intros S T c. induction c.
- introv P1 R H HT. Inverts R. Inverts H. Invstep HT. split; Simpl. constructor.  
- introv P1 R H HT. Inverts R. Inverts H. Invstep HT. split; Simpl. constructor.  
- introv P1 R H HT. Inverts R. Inverts H. Inverts HT. SimpS. Rpure.
  apply IHc1 with (c':=c1') (s:=s) (c'':= c1'') (t:=t0)  in H3; Simpl. 
  apply IHc2 with (c':=c2'0) (c'':=c2'') (t:=t) in H11 ; Simpl.
  split; Simpl. repeat constructor; easy.
- introv P1 R H HT. Dd_buset t2. Inverts R. unfold SWAP_LR in HT. unfold  SWAP_LS in HT.
  Invstep HT. SimpS. Inverts H13.  
  apply IHc1 with  (c2':=x18) (t2:={x9, {x11, x12, x10}}) (s:=x1) (t:=x) (f:=f)  in H3; try easy.
  SimpS.
  apply IHc2 with (c3:=c22) (c2':=x40) (t2:={x14, {x16, x17, x15}}) (s:=x2) (t:=x0) (f:=x3)in H9;
  try easy. SimpS. split; Simpl; constructor; try easy.
- introv P1 R H HT. Dd_buset t2. Inverts R. Inverts H. Inverts H8.
  unfold memBlock in HT. unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS. 
  apply step_rhs in H16. SimpS. Rpure.
  Destruct_s f; destruct x.
  + apply step_lhs with  (sav:=true) (rol:=false) 
                             (d:= d) (r:= r) (fai:=false) in H19; try easy.
    SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1. 
    apply IHc with (c':=c'0) (c'':=c''0) (t:={t, a}) in H2; try easy. SimpS.
    split. exists x; easy. simpl. repeat constructor; try easy. Simpl. constructor; Checkpure. 
  + apply step_lhs with  (sav:=true) (rol:=false) (d:= d) (r:= r) (fai:=true) in H19; try easy.
    SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1.
    apply IHc with (c':=c'0) (c'':=c''0) (t:={t, a}) in H2; try easy. SimpS.
    split. exists x; easy. simpl. repeat constructor; try easy. Simpl. constructor; Checkpure. 
  + apply step_lhs_f with  (sav:=true) (rol:=false) (d:= d) (r:=r) in H19; try easy.
    SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1.
    apply IHc with (c':=c'0) (c'':=c''0)(t:={t, a}) in H2; try easy. SimpS.
    split. exists x; easy. simpl. repeat constructor; try easy. Simpl. constructor; Checkpure.
Qed. 

(**if d' and r memory cells are corruted and control signals are (save, rollback, fail)=~1,1,1}*)
(*then the next clock cycle, r' and r become corrupted*)
Lemma step1_mb_d'r : forall S T (c c' c'':circuit S T) cc cc' t2 s t,
                       pure_bset s -> dtr1_d'r c c' c'' cc
                    -> step c s t c'
                    -> step cc {s,{~1,~1,~1}} t2 cc'
                    -> t2 = {t,{~1,~1,~1}} /\ dtrec_rr' c'' c' cc'.
Proof.
introv P R H HT. induction H.
- Inverts R; split; Invstep HT; Simpl. constructor.
- Inverts R; split; Invstep HT; Simpl. constructor.
- Inverts R. Inverts HT.
  Apply IHstep1 in H6;  Simpl.
  Apply IHstep2 in H12; Simpl. split; Simpl. constructor; easy.
- Inverts R. unfold SWAP_LS in HT. unfold SWAP_LR in HT.
  Invstep HT. SimpS.
  Apply IHstep1 in H0; Simpl.
  Apply IHstep2 in H10; Simpl.
  split; Simpl. constructor; easy.
- Inverts R. unfold memBlock in HT. 
  unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS.
  apply step_rhs in H17. 
  apply step_lhs  with (d:=d) (r:=r)(sav:=true) (rol:=true) (fai:=true) in H20; try easy.
  SimpS. simpl in H1. simpl in H2. 
  assert (HX:(negb (eqb d' d) || true)=true) by (destruct (negb (eqb d' d)); easy). (*[B]*)
  rewrite HX in H2. unfold bool2bset in H2. simpl in H2. Inverts H10.
  apply IHstep with (c'':=c''0) in H2. SimpS.
  split; Simpl; constructor; try easy. constructor. Checkpure. easy.
Qed.

(**if r' and r checkpointing memory cells are corruted and control signals are (save, rollback, fail)=~1,0,unknown}*)
(*then the next clock cycle, only r' stay to be corrupted*)
Lemma step1_mb_rr' : forall S T (c c' c'':circuit S T) c2 c2' t2 s t f, 
                       pure_bset s -> dtr1_rr' c c' c'' c2 
                    -> step c' s t c''
                    -> step c2 {s,{~1,~0,f}} t2 c2'
                    -> (exists b, t2 = {t,{~1,~0,b}}) /\ dtr0_r' c' c'' c2'.
Proof. 
intros S T c. induction c.
- introv P1 R H HT. Inverts R. Inverts H. Invstep HT. split; Simpl. constructor.  
- introv P1 R H HT. Inverts R. Inverts H. Invstep HT. split; Simpl. constructor.  
- introv P1 R H HT. Inverts R. Inverts H. Inverts HT. SimpS. Rpure.
  apply IHc1 with (c':=c1') (s:=s) (c'':= c1'') (t:=t0)  in H3; Simpl. 
  apply IHc2 with (c':=c2'0) (c'':=c2'') (t:=t) in H11 ; Simpl.
  split; Simpl. repeat constructor; easy.
- introv P1 R H HT. Dd_buset t2. Inverts R. unfold SWAP_LR in HT. unfold  SWAP_LS in HT.
  Invstep HT. SimpS. Inverts H13.  
  apply IHc1 with  (c2':=x18) (t2:={x9, {x11, x12, x10}}) (s:=x1) (t:=x) (f:=f)  in H3; try easy.
  SimpS.
  apply IHc2 with (c3:=c22) (c2':=x40) (t2:={x14, {x16, x17, x15}}) (s:=x2) (t:=x0) (f:=x3)in H9;
  try easy. SimpS. split; Simpl; constructor; try easy.
- introv P1 R H HT. Dd_buset t2. Inverts R. Inverts H. Inverts H8.
  unfold memBlock in HT. unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS. 
  apply step_rhs in H16. SimpS. Rpure.
  Destruct_s f; destruct x.
  + apply step_lhs with  (sav:=true) (rol:=false) 
                             (d:= d) (r:= r) (fai:=false) in H19; try easy.
    SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1. 
    apply IHc with (c':=c'0) (c'':=c''0) (t:={t, a}) in H2; try easy. SimpS.
    split. exists x; easy. simpl. repeat constructor; try easy. Simpl. constructor; Checkpure. 
  + apply step_lhs with  (sav:=true) (rol:=false) (d:= d) (r:= r) (fai:=true) in H19; try easy.
    SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1.
    apply IHc with (c':=c'0) (c'':=c''0) (t:={t, a}) in H2; try easy. SimpS.
    split. exists x; easy. simpl. repeat constructor; try easy. Simpl. constructor; Checkpure. 
  + apply step_lhs_f with  (sav:=true) (rol:=false) (d:= d) (r:=r) in H19; try easy.
    SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1.
    apply IHc with (c':=c'0) (c'':=c''0)(t:={t, a}) in H2; try easy. SimpS.
    split. exists x; easy. simpl. repeat constructor; try easy. Simpl. constructor; Checkpure.
Qed.

(**if only r' checkpointing memory cell is corruted and control signals are (save, rollback, fail)=~1,0,unknown}*)
(*then the next clock cycle, the memory block state is correct*)
Lemma step1_mb_r' : forall S T (c c' c'':circuit S T) c2 c2' t2 s t f, 
                      pure_bset s -> dtr1_r' c c' c'' c2 
                   -> step c' s t c''
                   -> step c2 {s,{~1,~0,f}} t2 c2'
                   -> (exists b, t2 = {t,{~1,~0,b}}) /\ dtrs0 c' c'' c2'.
Proof. 
intros S T c. induction c; unfold dtrs0.
- introv P1 R H HT. Inverts R. Inverts H. Invstep HT. split; Simpl.
- introv P1 R H HT. Inverts R. Inverts H. Invstep HT. split; Simpl.
- introv P1 R H HT. Inverts R. Inverts H. Inverts HT. SimpS. Rpure.
  apply IHc1 with (c':=c1') (s:=s) (c'':= c1'') (t:=t0)  in H3; Simpl. 
  apply IHc2 with (c':=c2'0) (c'':=c2'') (t:=t) in H11 ; Simpl.
- introv P1 R H HT. Dd_buset t2. Inverts R. unfold SWAP_LR in HT. unfold  SWAP_LS in HT.
  Invstep HT. SimpS. Inverts H13.  
  apply IHc1 with  (c2':=x18) (t2:={x9, {x11, x12, x10}}) (s:=x1) (t:=x) (f:=f)  in H3; try easy.
  SimpS.
  apply IHc2 with (c3:=c22) (c2':=x40) (t2:={x14, {x16, x17, x15}}) (s:=x2) (t:=x0) (f:=x3)in H9;
  try easy. SimpS. split; Simpl; constructor; try easy.
- introv P1 R H HT. Dd_buset t2. Inverts R. Inverts H. Inverts H8.
  unfold memBlock in HT. unfold lhsMB in HT. unfold rhsMB in HT. Invstep HT. SimpS. 
  apply step_rhs in H16. SimpS. Rpure.
  Destruct_s f; destruct x.
  + apply step_lhs with  (sav:=true) (rol:=false) 
                             (d:= d) (r:= r) (fai:=false) in H19; try easy.
    SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1. 
    apply IHc with (c':=c'0) (c'':=c''0) (t:={t, a}) in H2; try easy. SimpS.
    split. exists x; easy. simpl. repeat constructor; try easy. Simpl. constructor; Checkpure. 
  + apply step_lhs with  (sav:=true) (rol:=false) (d:= d) (r:= r) (fai:=true) in H19; try easy.
    SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1.
    apply IHc with (c':=c'0) (c'':=c''0) (t:={t, a}) in H2; try easy. SimpS.
    split. exists x; easy. simpl. repeat constructor; try easy. Simpl. constructor; Checkpure. 
  + apply step_lhs_f with  (sav:=true) (rol:=false) (d:= d) (r:=r) in H19; try easy.
    SimpS. unfold bool2bset in H2. simpl in H2. simpl in H1.
    apply IHc with (c':=c'0) (c'':=c''0)(t:={t, a}) in H2; try easy. SimpS.
    split. exists x; easy. simpl. repeat constructor; try easy. Simpl. constructor; Checkpure.
Qed.

(*Possible consequences of a glitch during even clock cycle if before the state was correct*)
Lemma stepg1_mb : forall  S T (c c' c'':circuit S T) c2 c2' t2 s t f, 
                   pure_bset s -> pure_bset f ->  dtrs1 c c' c'' c2 
                -> step c' s t c''
                -> stepg c2 {s,{~1,~0,f}} t2 c2'
                -> 
(  (exists b,     t2 = {t, {~1,~0,bool2bset b}}) /\ dtr0_r   c' c'' c2' )  (*r cell is corrupted *)
\/((exists b,     t2 = {t, {~1,~0,bool2bset b}}) /\ dtr0_r'  c' c'' c2' )  (*r' cell is corrupted *)
\/((exists e1 e2, t2 = {e1,{~1,~0,e2}})          /\ dtr0_dr  c' c'' c2' )  (*glitch after d'-> input, d, and r corrupted*)
\/((exists  e1,   t2 = {t, {~1,~0,e1}})          /\ dtr0_d'  c' c'' c2' ). (*glitch before d' kills d' and fail output*)
Proof.
intros S T c. induction c.
- introv P1 P2 R H HT. Inverts R. Inverts H. Inverts HT; Dd_buset v; Inverts H11; Inverts H3. 
  Inverts H. Inverts H8.
  + rewrite <- H. right. right. left. split; repeat constructor. Simpl.
  + rewrite <- H. right. right. left. split; repeat constructor. Simpl.
  + rewrite <- H1. right. right. left. split; repeat constructor. Simpl.
  + rewrite <- H1. right. right. left. split; repeat constructor. Simpl.
  + left. split; repeat constructor.  exists (fbset2bool x0). rewrite rew_bool2bsetf; Simpl.
  + Inverts H. right. right. left. split; repeat constructor. Simpl.
- introv P1 P2 R H HT. Inverts R. Inverts H. Inverts HT; Dd_buset v; Inverts H11. Inverts H3. 
  Inverts H.
  + left. split. exists (fbset2bool x0). rewrite rew_bool2bsetf; Simpl. constructor.
  + right. right. left. Inverts H. Inverts H3. split; repeat constructor. Simpl.
- introv P1 P2 R H HT. Inverts R. Inverts H. Inverts HT. SimpS.  
  + apply IHc1 with (c':=c1') (c'':=c1'') (t:=t0 ) in H3; try easy.
    destruct H3 as [H|[H|[H|H]]]; SimpS. 
    * apply step1_mb with (c2':= c2'1) (t2:= {x1, {x4, x7, x6}}) (s:=t0)
      (t:=t) (f:= bool2bset x5) in H9; try easy. SimpS.
      left. split; repeat constructor; apply dtrs0_imp_dtr0_r in H1; try easy.
      Simpl. Simpl. Checkpure.
    * apply step1_mb  with (c:=c2) (c2:=c22) (c2':=c2'1) 
      (t2:= {x1, {x4, x7, x6}}) (f:= bool2bset x5)in H12; try easy. SimpS.
      right. left. split; repeat constructor; apply dtrs0_imp_dtr0_r' in H1; try easy.
      Simpl. Simpl. Checkpure.
    * apply step1_mb_if with (c:=c2) (c':=c2'0) (c'':=c2'') in H11; try easy. SimpS.
      right. right. left. split; repeat constructor; Simpl.
    * apply step1_mb_f with (c:=c2) (c':=c2'0) (c'':=c2'') (t:=t) in H11; try easy. SimpS.
      right. right. right. split; repeat constructor; Simpl; apply dtrs0_imp_dtr0_d' in H1; easy. Simpl.
  + apply step1_mb with (c:=c1) (c':=c1') (c'':=c1'') (t:=t0) in H3; try easy. SimpS.
    apply IHc2 with (c':=c2'0) (c'':=c2'' ) (t:=t) in H11; Simpl.
    destruct H11 as [H|[H|[H|H]]]; SimpS.
    * left. split; repeat constructor; apply dtrs0_imp_dtr0_r in H0; Simpl.
    * right. left. split; repeat constructor; apply dtrs0_imp_dtr0_r' in H0; Simpl. 
    * right. right. left.  split; repeat constructor; apply dtrs0_imp_dtr0_dr in H0; Simpl.
    * right. right. right. split; repeat constructor; apply dtrs0_imp_dtr0_d' in H0; Simpl.
    * Checkpure. 
 -  introv P1 P2 R H HT. Inverts R. Inverts H. unfold SWAP_LS in HT. unfold SWAP_LR in HT. Invstep HT;
    SimpS.
  + apply IHc1  with (c':=c1') (c'':=c1'') (t:=t0) in H; try easy.
    destruct H as [H|[H|[H|H]]]; SimpS.
    * apply step1_mb  with (c:=c2) (c':=c2'0) (c'':=c2'') (t:=v) in H2; try easy. SimpS.
      left. split; repeat constructor; apply dtrs0_imp_dtr0_r in H2; try easy. Simpl. Checkpure.
    * apply step1_mb  with (c:=c2) (c':=c2'0) (c'':=c2'') (t:=v) in H2; try easy. SimpS.
      right. left. split; repeat constructor; apply dtrs0_imp_dtr0_r' in H2; try easy. Simpl. Checkpure.
    * apply step1_mb_f with (c:=c2) (c':=c2'0) (c'':=c2'') (t:=v) in H2; try easy. SimpS.
      right. right. left. split; repeat constructor; Simpl; apply dtrs0_imp_dtr0_dr in H2; easy.
    * apply step1_mb_f with (c:=c2)(c':=c2'0) (c'':=c2'') (t:=v) in H2; try easy. SimpS.
      right. right. right. split; repeat constructor; Simpl; apply dtrs0_imp_dtr0_d' in H2; easy.
  + apply step1_mb  with (c:=c1) (c':=c1') (c'':=c1'') (t:=t0) in H; try easy. SimpS. 
    apply IHc2 with  (c':=c2'0) (c'':=c2'') (t:=v) in H1; try easy. destruct H1 as [H|[H|[H|H]]]; SimpS.
    * left. split; repeat constructor; apply dtrs0_imp_dtr0_r in H5; Simpl. 
    * right. left. split; repeat constructor; apply dtrs0_imp_dtr0_r' in H5; Simpl. 
    * right. right. left. split; repeat constructor; Simpl; apply dtrs0_imp_dtr0_dr in H5; Simpl.
    * right. right. right. split; repeat constructor; Simpl; apply dtrs0_imp_dtr0_d' in H5; easy.
    * Checkpure.  
-introv P1 P2 R H HT. Dd_buset t2. Inverts R. Inverts H8. Inverts H.
 Apply invstepgDTRloop1 in HT. unfold mbgG in HT. 
 destruct HT as [H|[H|[H|[H|H]]]]. 
 +unfold mbg12 in H. SimpS.
  apply step_rhs in H3.
  apply stepg1_lhs  with  (d:=d) (fai:=fbset2bool f) (r'_I:=bool2bset r') in H1; try easy.
  SimpS. destruct H1 as [Hx1|[[Hx2|[Hx3|Hx4]] Hx1]]; SimpS; simpl in H.
   * apply step1_mb with  (c:=c) (c':=c'0) (c'':=c''0) (t:={t,a}) in H0; try easy. SimpS.
     assert (HX:x4=x5) by (Destruct_s a; Simpl); Inverts HX.
     right. left. split; Simpl. repeat constructor. apply dtrs0_imp_dtr0_r' in H1; easy.  Simpl.
     rewrite rew_fbset2bool. constructor. Checkpure. Checkpure. 
   * apply step1_mb_i with (c:=c) (c':=c'0) (c'':=c''0) in H0; try easy. SimpS.
     right. right. left. split. exists x1 (bool2bset x0). easy.
     constructor. easy. rewrite rew_fbset2bool. rewrite rew_fbset2bool. constructor. Checkpure.
   * apply step1_mb_if with  (c:=c) (c':=c'0) (c'':=c''0) in H0; try easy. SimpS.
     right. right. left.  split. exists x1 x0. easy. constructor. easy.
     rewrite rew_fbset2bool. rewrite rew_fbset2bool. constructor.
   * apply step1_mb_f with  (c:=c) (c':=c'0) (c'':=c''0) (t:={t, a})in H0; try easy.
     SimpS. right. right. left.  split. exists t x0.  easy. constructor. apply dtrs0_imp_dtr0_dr in H1.
     easy. rewrite rew_fbset2bool. rewrite rew_fbset2bool. constructor. Checkpure.
   * rewrite rew_bool2bsetf; Simpl. 
 + unfold mbg13 in H. SimpS.
   apply step_rhs in H3.
   apply step_lhs with (sav:=true) (rol:=false)
   (d:= d) (r:= r) (fai:=fbset2bool f) in H1; try easy. SimpS.
   simpl in H. simpl in H0. unfold bool2bset in H0. simpl in H0.
   apply IHc with (c':=c'0) (c'':=c''0) (t:={t,a}) in H0; try easy. SimpS.
   destruct H0 as [[H1 Hx2]| [Hx2|[H1|H1]]]; SimpS.
   * left. split; Simpl. repeat constructor. easy.
   * right. left. split; Simpl. repeat constructor. easy.
   * right. right. left. split. exists x1 x0. easy. repeat constructor. easy.
   * right. right. right. split; Simpl. repeat constructor. easy.
   * Checkpure. * Checkpure. * rewrite rew_bool2bsetf; Simpl.
 + unfold mbg16 in H. SimpS.
   apply step_lhs with(sav:=true) (rol:=false)
   (d:= d) (r:= r) (fai:=fbset2bool f)  in H1; try easy. SimpS.
   simpl in H0. unfold bool2bset in H0. simpl in H0.
   apply step1_mb with (c:=c) (c':=c'0) (c'':=c''0) (t:={t,a})  in H0; try easy. SimpS.
   apply stepg_rhs with (si:=fbset2bool a) (sav2:= true) 
   (sav:= true) (fai:= x1) (rol:=false) (r:=r) in H3; try easy. SimpS. 
   destruct H3; SimpS.
   * left. split; Simpl. repeat constructor.
     apply dtrs0_imp_dtr0_r in H1. Simpl.
   * left. split; Simpl. repeat constructor.
     apply dtrs0_imp_dtr0_r in H1. easy. 
   * rewrite rew_bool2bsetf; Simpl. 
   * Checkpure. * Checkpure. * rewrite rew_bool2bsetf; Simpl. 
 + unfold mbg17 in H. destruct H; SimpS.
   apply step_rhs in H4. SimpS.
   Inverts H3. (*case: after invertion of introglitch*)
   * apply step_lhs_r with  (sav:=true) (rol:=false)
     (d:= d)  (fai:=fbset2bool f) in H1; try easy. SimpS.
     simpl in H. unfold bool2bset in H0. simpl in H0.
     apply step1_mb  with (c:=c) (c':=c'0) (c'':=c''0) (t:={t,a})   in H0;
     try easy. destruct H3; SimpS; right; left; split; Simpl; repeat constructor;
     apply dtrs0_imp_dtr0_r' in H3; simpl; Simpl. Checkpure. Checkpure.
     rewrite rew_bool2bsetf; Simpl.
   * symmetry in H4; destruct r; Inverts H4. unfold bool2bset in H1. simpl in H1.
     apply step_lhs_r with (sav:=true) (rol:=false)
                          (d:= d) (fai:=fbset2bool f) in H1; try easy.
     simpl in H1. destruct H1; SimpS. simpl in H.  unfold bool2bset in H0. simpl in H0. 
     apply step1_mb with (c:=c) (c':=c'0) (c'':=c''0) (t:={t,a})  in H0; try easy. SimpS.
     assert (HX:x4=x5) by (Destruct_s a; Simpl); Inverts HX.
     right. left. split; Simpl. destruct H3; SimpS; repeat constructor;
     apply dtrs0_imp_dtr0_r' in H1; easy. Checkpure. rewrite rew_bool2bsetf; Simpl.
   * apply step_lhs with  (sav:=true) (rol:=false)
                    (d:= d) (r:= r) (fai:=fbset2bool f) in H1; try easy. SimpS.
     apply step1_mb with (c:=c) (c':=c'0) (c'':=c''0) (t:={t,a})  in H0. SimpS.
     simpl in H. assert (HX:x4=x5) by (Destruct_s a; Simpl); Inverts HX.
     left. split. Simpl. constructor. apply dtrs0_imp_dtr0_r in H1. easy. simpl. 
     Simpl. constructor. Checkpure. Checkpure. easy. simpl. easy. 
     rewrite rew_bool2bsetf; Simpl.
 + unfold mbg18 in H. destruct H; SimpS.
   apply step_rhs in H4. SimpS.
   Inverts H3. (*case: after invertion of introglitch*)
   * apply step_lhs_i with  (sav:=true) (rol:=false)
     (r:= r)  (fai:=fbset2bool f) in H1; try easy. SimpS.
     simpl in H. unfold bool2bset in H0. simpl in H0.
     apply step1_mb_f with (c:=c) (c':=c'0) (c'':=c''0) (t:={t,a}) in H0;
     try easy. destruct H3; SimpS; right; right; right; split; Simpl; repeat constructor;
     apply dtrs0_imp_dtr0_d' in H3; easy. Checkpure. rewrite rew_bool2bsetf; Simpl.
   * symmetry in H4; destruct d; Inverts H4. unfold bool2bset in H1. simpl in H1.
     apply step_lhs_i with (sav:=true) (rol:=false) (r:= r)  (fai:=fbset2bool f)in H1; try easy.
     simpl in H1. destruct H1; SimpS. simpl in H.  unfold bool2bset in H0. simpl in H0. 
     apply step1_mb_f with (c:=c) (c':=c'0) (c'':=c''0) (t:={t,a})  in H0; try easy. SimpS.
     right. right. right. split; Simpl. destruct H3; SimpS; repeat constructor;
     apply dtrs0_imp_dtr0_d' in H1; easy. Checkpure. rewrite rew_bool2bsetf; Simpl.
   * apply step_lhs with  (sav:=true) (rol:=false)
     (d:= d) (r:= r)   (fai:=fbset2bool f ) in H1; try easy. SimpS.
     simpl in H. unfold bool2bset in H0. simpl in H0.
     apply step1_mb with (c:=c) (c':=c'0) (c'':=c''0) (t:={t,a})  in H0;
     try easy. SimpS. left. split; Simpl. repeat constructor;
     apply dtrs0_imp_dtr0_r in H1; easy. Checkpure. Checkpure. rewrite rew_bool2bsetf; Simpl.
Qed.
