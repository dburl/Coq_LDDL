(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-   Basic properties of output buffers

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import dtrTransform outputStep.

Set Implicit Arguments.


(* ####################################################### *)
(** *     Output Buffer Properties                         *)
(* ####################################################### *)

(** Glitch within the output buffer (ie not on input wires)    *)
(*     Even cycles (save=1, fail=rollBack=subst=0)  p={b,b',f} *)
(*               by reflection                                 *)

Lemma stepg1_ob_R : forall p t c,
                   ((fun p => pure_bset p) p)
                  -> stepg ((fun p => let b := fbset2bool (fstS(fstS p)) in
                                      let b':= fbset2bool (sndS(fstS p)) in
                                      outBufDTR b b' b b' b') p)
                           ((fun p =>{fstS(fstS p), {~ 1, ~ 0, sndS p, ~ 0}}) p) t c
                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in
                               let b := fbset2bool (fstS(fstS p)) in
                               let b' := fbset2bool (sndS(fstS p)) in
                               let r := sndS(fstS p) in 
                               ( (fstS (fstS t) = r /\ (fstS (sndS (fstS t))=r \/ sndS(sndS (fstS t))=r))
                                   \/ (fstS (sndS (fstS t))=r /\ sndS(sndS (fstS t))=r))
                                 /\ (    c=outBufDTR b true b b b'
                                     \/ c=outBufDTR b false b b b'
                                     \/ c=outBufDTR b b b true b'
                                     \/ c=outBufDTR b b b false b'
                                     \/ c=outBufDTR b b b b true
                                     \/ c=outBufDTR b b b b false)) (p,t,c). 

Proof. introv. Reflect_step_g.  Destruct_s s. Simpl. Qed.



Lemma stepg1_ob : forall b b' f t c,
                 stepg (outBufDTR b b' b b' b') {bool2bset b,{~1,~0, bool2bset f,~0}} t c
              -> (exists x, fstS t={x,{bool2bset b',bool2bset b'}}
                         \/ fstS t={bool2bset b',{x,bool2bset b'}} \/ fstS t={bool2bset b',{bool2bset b',x}})
              /\ (exists z, c=outBufDTR b z b b b'
                         \/ c=outBufDTR b b b z b' \/ c=outBufDTR b b b b z).
Proof. 
introv H.
set (p := {bool2bset b,bool2bset b',bool2bset f}).
assert (X1: fbset2bool (fstS(fstS p)) =  b)
   by (replace p with {bool2bset b,bool2bset b',bool2bset f}; destruct b; easy).
assert (X2: fbset2bool (sndS(fstS p)) = b')
   by (replace p with {bool2bset b,bool2bset b',bool2bset f}; destruct b'; easy).
rewrite <- X1 in H at 1 2. rewrite <- X2 in H.
eapply stepg1_ob_R in H; try CheckPure.
simpl fst in H. rewrite X1 in H. rewrite X2 in H. clear X1. clear X2.
Dd_buset t.
destruct H as [[[H0 [H1|H1]]|[H0 H2]] [H|[H|[H|[H|[H|H]]]]]]; cbn in *; subst; split;
try (exists x; easy); try (exists x1; easy); try (exists x2; easy); try (exists x3; easy); 
try (exists false; easy); try (exists true; easy).
Qed.


(*     Odd cycles (save=rollBack=subst=fail=0)  p={b,b',b'',f} *)
(*               by reflection                                 *)

Lemma stepg0_ob_R : forall p t c,
                   ((fun p => pure_bset p) p)
                  -> stepg ((fun p => let b  := fbset2bool (fstS(fstS (fstS p))) in
                                      let b' := fbset2bool (sndS(fstS (fstS p))) in
                                      let b'':= fbset2bool (sndS(fstS p)) in
                                      outBufDTR b' b' b' b' b'') p)
                           ((fun p =>{fstS(fstS (fstS p)), {~ 0, ~ 0, sndS p, ~ 0}}) p) t c
                  -> (fun e => let p    := fst(fst e) in 
                               let t    := snd(fst e) in
                               let c    := snd e in
                               let b    := fbset2bool (fstS(fstS (fstS p))) in
                               let b'   := fbset2bool (sndS(fstS (fstS p))) in
                               let b''  := fbset2bool (sndS(fstS p)) in
                               let rb'  := sndS(fstS (fstS p)) in 
                               let rb'' := sndS(fstS p) in 
                               (sndS t = sndS p /\ (c=outBufDTR b true b b' b'
                                                      \/ c=outBufDTR b false b b' b'))
                                     \/ c=outBufDTR b b' b true b'
                                     \/ c=outBufDTR b b' b false b'
                                     \/ c=outBufDTR b b' b b' true
                                     \/ c=outBufDTR b b' b b' false) (p,t,c). 

Proof. introv. Reflo_step_g. Destruct_s s. Simpl. Qed.

Lemma stepg0_ob : forall b b' b'' f t c,
                  stepg (outBufDTR b' b' b' b' b'') {bool2bset b,{~0,~0,bool2bset f,~0}} t c
               -> exists z, (sndS t= bool2bset f /\ c=outBufDTR b z b b' b')
                          \/ c=outBufDTR b b' b z b' \/ c=outBufDTR b b' b b' z.
Proof. 
introv H.
set (p := {bool2bset b,bool2bset b',bool2bset b'',bool2bset f}).
assert (X1: fbset2bool  (sndS p) =  f)
  by (replace p with {bool2bset b,bool2bset b',bool2bset b'',bool2bset f}; destruct f; easy).
assert (X2: fbset2bool (sndS(fstS(fstS p))) = b')
   by (replace p with {bool2bset b,bool2bset b',bool2bset b'',bool2bset f}; destruct b'; easy).
assert (X3: fbset2bool (sndS (fstS p)) = b'')
   by (replace p with {bool2bset b,bool2bset b',bool2bset b'',bool2bset f}; destruct b''; easy).
rewrite <- X2 in H. rewrite <- X3 in H. 
eapply stepg0_ob_R in H; try CheckPure.
simpl fst in H. Dd_buset t. 
simpl fstS in H. simpl sndS in H. simpl snd in H. clear X2. clear X3.
repeat rewrite rew_fbset2bool in H.
destruct H as [[H1 [H|H]] |[H|[H|[H|H]]]]; 
try (exists x; easy); try (exists x1; easy); try (exists x3; easy); 
try (exists false; easy); try (exists true; easy).
Qed.


(* ####################################################### *)
(** *     Output Buffer Bank Properties                     *)
(* ####################################################### *)

(** Property of output buffer bank when a glitch occurs within  *)
Lemma stepg1_obs : forall S (p p':{|S|}) f t c, 
                      pure_bset p -> pure_bset p' -> pure_bset f
                   -> stepg (dtrOB_T p p' p p' p') {p,{~1,~0,f,~0}} t c 
                   -> (exists x, fstS t={x,{p',p'}} \/ fstS t={p',{x,p'}} \/ fstS t={p',{p',x}})
                   /\ (exists z, pure_bset z /\ (c=dtrOB_T p z p p p' \/ c=dtrOB_T p p p z p' 
                     \/ c=dtrOB_T p p p p z)).
Proof.
induction S; introv P1 P2 P3 H. 
- cbn in H.
  assert (X: p = bool2bset(fbset2bool p))
  by (Destruct_s p; destruct x; Inverts P1; try easy).
  rewrite X in H at 3. clear X.
  assert (X: f = bool2bset(fbset2bool f))
  by (Destruct_s f; destruct x; Inverts P3; try easy).
  rewrite X in H. clear X.
  apply stepg1_ob in H; try easy.
  apply rew_bool2bsetf in P2. rewrite P2 in  H.
  destruct H as [[x [H|[H|H]]] H1]; split;
  try (exists x; easy);
  destruct H1 as [z [H1|[H1|H1]]]; destruct z;
  try (exists (~1); easy); try (exists (~0); easy). 
- Dd_buset_all. cbn in H.
  Invstep H; SimpS.
  + apply fact_plug1_OB in H. apply fact_plug2_OB in H4. SimpS.
    Apply IHS1 in H8. SimpS.
    Apply step_obs_sf in H3. SimpS.
    apply fact_plug3_OB in H2. SimpS. 
    simpl fstS. destruct H as [H|[H|H]]; SimpS; 
    split; try (exists {x1,x12}; easy); 
    destruct H7 as [?|[?|?]]; SimpS; 
    try (exists {x4,x53}; easy); 
    try (exists {x2,x53}; easy);
    try (exists {x2,x55}; easy).
+  apply fact_plug1_OB in H. apply fact_plug2_OB in H2. SimpS.
    Apply step_obs_sf in H5. SimpS.
    Apply IHS2 in H4; try CheckPure. SimpS.
    apply fact_plug3_OB in H1. SimpS. 
    simpl fstS. destruct H as [H|[H|H]]; SimpS; 
    split; try (exists {x1,x12}; easy);
    destruct H4 as [?|[?|?]]; SimpS; 
    try (exists {x48,x4}; easy); 
    try (exists {x50,x2}; easy);
    try (exists {x48,x2}; easy).
    Apply pure_orS.
Qed.

(** Property of output buffer bank when a glitch occurs within  *)


Lemma stepg0_obs : forall S (p p' p'':{|S|}) f t c, 
                   pure_bset p -> pure_bset p' -> pure_bset p'' -> pure_bset f
               -> stepg (dtrOB_T p' p' p' p' p'') {p,{~0,~0,f,~0}} t c 
               -> (exists z, pure_bset z 
                         /\ (  (sndS t = f /\ c=dtrOB_T p z p p' p')
                            \/  c=dtrOB_T p p' p z p' 
                            \/  c=dtrOB_T p p' p p' z)).
Proof. 
induction S; introv P1 P2 P3 P4 H. 
- cbn in H.
  assert (X: p = bool2bset(fbset2bool p))
  by (Destruct_s p; destruct x; Inverts P1; try easy).
  rewrite X in H. clear X.
  assert (X: f = bool2bset(fbset2bool f))
  by (Destruct_s f; destruct x; Inverts P4; try easy). 
  rewrite X in H. clear X.
  apply stepg0_ob in H; try easy.
  destruct H as [x H].
  replace x with (fbset2bool (bool2bset x)) in H. 2: rewrite rew_fbset2bool; easy.
  apply b2bs_equiv_fb2bs in P4. rewrite P4 in H. 
  destruct H as [[? H]|[H|H]]; 
  exists (bool2bset x); split; try CheckPure; try easy.
- Dd_buset_all. cbn in H.
  Invstep H; SimpS.
  + apply fact_plug1_OB in H. apply fact_plug2_OB in H4. SimpS.
    Apply IHS1 in H8. SimpS.
    Apply step_obs_sf in H3. SimpS.
    apply fact_plug3_OB in H2. SimpS. 
    destruct H4 as [[? ?]|[?|?]]; subst.
    * exists {x2,x55}. split. easy. left.
      split. rewrite beq_buset_reflx. rewrite rew_orS5. easy. easy.
    * exists {x2,x55}; easy.
    * exists {x2, x55}; easy.
+  apply fact_plug1_OB in H. apply fact_plug2_OB in H2. SimpS.
    Apply step_obs_sf in H5. SimpS.
    Apply IHS2 in H4; try CheckPure. simpl sndS in H4. SimpS.
    apply fact_plug3_OB in H1. SimpS. 
    destruct H2 as [[? ?]|[?|?]]; SimpS; exists {x50,x2}; split; try easy. 
    left. split. rewrite beq_buset_reflx. rewrite rew_orS5. easy. easy.
    Apply pure_orS.
Qed.
