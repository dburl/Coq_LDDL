(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-   Generic properties (i.e., for all states of the control block)      
    of output buffers.            

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)
(*
Add LoadPath "..\".
Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".*)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import dtrTransform.

Set Implicit Arguments.

Opaque orS.

(* ############################################################ *)
(** *      Properties of a single output buffer                 *)
(* ############################################################ *)

(** The save and fail signals may be corrupted; roolBack=0, subst=0 *)
(*  by reflection  p={p1,p2,o1,o2,o3,co,save,fail}                  *)
Lemma step_ob_sf_R : forall p t c, 
                     ((fun p => pure_bset (fstS(fstS p))) p)
                  -> step ((fun p => let p1 := fbset2bool(fstS(fstS(fstS(fstS(fstS(fstS(fstS p))))))) in
                                     let p2 := fbset2bool(sndS(fstS(fstS(fstS(fstS(fstS(fstS p))))))) in
                                     let o1 := fbset2bool(sndS(fstS(fstS(fstS(fstS(fstS p)))))) in
                                     let o2 := fbset2bool(sndS(fstS(fstS (fstS(fstS p))))) in
                                     let o3 := fbset2bool(sndS(fstS(fstS(fstS p)))) in
                                     outBufDTR p1 p2 o1 o2 o3) p)
                           ((fun p =>{sndS(fstS(fstS p)),{sndS(fstS p),~0, sndS p,~0}}) p) t c
                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in
                               let p1 := fstS(fstS(fstS(fstS(fstS(fstS(fstS p)))))) in
                               let p2 := sndS(fstS(fstS(fstS(fstS(fstS(fstS p)))))) in
                               let o1 := sndS(fstS(fstS(fstS(fstS(fstS p))))) in
                               let o2 := sndS(fstS(fstS(fstS(fstS p)))) in
                               let o3 := sndS(fstS(fstS(fstS p))) in 
                               let co := sndS(fstS(fstS p)) in 
                                (t={{p2,{o2,o3}},orS {(sndS p),
                                             (bool2bset (xorb (fbset2bool o1) (fbset2bool o2)))}})
                            /\ (snd e=outBufDTR (fbset2bool co) (fbset2bool p1) 
                                                (fbset2bool co) (fbset2bool o1) (fbset2bool o2))) (p,t,c).
Proof. introv. Reflo_step_g. Qed.

Lemma step_ob_sf : forall a p1 p2 o1 o2 o3 save fail t c, 
                   pure_bset a
                -> step (outBufDTR p1 p2 o1 o2 o3) {a,{save,~0, fail,~0}} t c 
                -> t={{bool2bset p2,{bool2bset o2,bool2bset o3}}, orS {fail,bool2bset(xorb o1 o2)}}
                /\ c=outBufDTR (fbset2bool a) p1 (fbset2bool a) o1 o2.
Proof. 
introv P H.
set (p := {bool2bset p1,bool2bset p2,bool2bset o1,bool2bset o2,bool2bset o3,a,save,fail}).
assert (X1: fbset2bool (fstS(fstS(fstS(fstS(fstS(fstS(fstS p)))))))= p1) 
    by (replace p with {bool2bset p1,bool2bset p2,bool2bset o1,bool2bset o2,bool2bset o3,a,save,fail}; destruct p1; easy).
assert (X2: fbset2bool (sndS(fstS(fstS(fstS(fstS(fstS(fstS p)))))))= p2) 
    by (replace p with {bool2bset p1,bool2bset p2,bool2bset o1,bool2bset o2,bool2bset o3,a,save,fail}; destruct p2; easy).
assert (X3: fbset2bool (sndS(fstS(fstS(fstS(fstS(fstS p))))))= o1) 
    by (replace p with {bool2bset p1,bool2bset p2,bool2bset o1,bool2bset o2,bool2bset o3,a,save,fail}; destruct o1; easy).
assert (X4: fbset2bool (sndS(fstS(fstS(fstS(fstS p)))))= o2) 
    by (replace p with {bool2bset p1,bool2bset p2,bool2bset o1,bool2bset o2,bool2bset o3,a,save,fail}; destruct o2; easy).
assert (X5: fbset2bool (sndS(fstS(fstS(fstS p))))= o3) 
    by (replace p with {bool2bset p1,bool2bset p2,bool2bset o1,bool2bset o2,bool2bset o3,a,save,fail}; destruct o3; easy).
rewrite <- X1 in H. rewrite <- X2 in H. rewrite <- X3 in H. rewrite <- X4 in H. rewrite <- X5 in H. 
apply step_ob_sf_R in H; try CheckPure.
simpl fst in H. simpl snd in H.
replace p with {bool2bset p1,bool2bset p2,bool2bset o1,bool2bset o2,bool2bset o3,a,save,fail} in H. 2: easy.
simpl fstS in H. simpl sndS in H.
repeat rewrite rew_fbset2bool in H.
easy.
Qed.


(** The input, fail and save signals may be corrupted; roolBack=0, subst=0 *)
(*  by reflection  p={p1,p2,o1,o2,o3,save,rb,fail,co}                      *)

Lemma step_ob_ibf_R : forall p t c, 
                     ((fun p => pure_bset (fstS(fstS(fstS p)))) p)
                  -> step ((fun p => let p1 := fbset2bool(fstS(fstS(fstS(fstS(fstS(fstS(fstS(fstS p)))))))) in
                                     let p2 := fbset2bool(sndS(fstS(fstS(fstS(fstS(fstS(fstS(fstS p)))))))) in
                                     let o1 := fbset2bool(sndS(fstS(fstS(fstS(fstS(fstS(fstS p))))))) in
                                     let o2 := fbset2bool(sndS(fstS(fstS (fstS(fstS(fstS p)))))) in
                                     let o3 := fbset2bool(sndS(fstS(fstS(fstS(fstS p))))) in
                                     outBufDTR p1 p2 o1 o2 o3) p)
                           ((fun p =>{sndS p,{sndS(fstS(fstS(fstS p))),sndS(fstS(fstS p)),sndS(fstS p),~0}}) p) t c
                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in
                               let p1 := fstS(fstS(fstS(fstS(fstS(fstS(fstS(fstS p))))))) in
                               let p2 := sndS(fstS(fstS(fstS(fstS(fstS(fstS(fstS p))))))) in
                               let o1 := sndS(fstS(fstS(fstS(fstS(fstS(fstS p)))))) in
                               let o2 := sndS(fstS(fstS(fstS(fstS(fstS p))))) in
                               let o3 := sndS(fstS(fstS(fstS(fstS p)))) in 
                                (t={{p2,{o2,o3}},orS {(sndS(fstS p)),
                                             (bool2bset (xorb (fbset2bool o1) (fbset2bool o2)))}})
                            /\ (snd e=outBufDTR true  (fbset2bool p1) true  (fbset2bool o1) (fbset2bool o2)
                             \/ snd e=outBufDTR false (fbset2bool p1) true  (fbset2bool o1) (fbset2bool o2)
                             \/ snd e=outBufDTR true  (fbset2bool p1) false (fbset2bool o1) (fbset2bool o2)
                             \/ snd e=outBufDTR false (fbset2bool p1) false (fbset2bool o1) (fbset2bool o2))) (p,t,c).
Proof. introv. Reflo_step_g. Qed.

(** The property in a more useable form  *)
Lemma step_ob_ibf : forall z p1 p2 o1 o2 o3 save rb fail t c, 
                      pure_bset save
                   -> step (outBufDTR p1 p2 o1 o2 o3) {z,{save,rb,fail,~0}} t c 
                   -> t={{bool2bset p2,{bool2bset o2,bool2bset o3}},
                          orS {fail,bool2bset (xorb o1 o2)}}
                   /\ (exists x y, c=outBufDTR x p1 y o1 o2).
Proof.  
introv P H.
set (p := {bool2bset p1,bool2bset p2,bool2bset o1,bool2bset o2,bool2bset o3,save,rb,fail,z}).
assert (X1: fbset2bool (fstS(fstS(fstS(fstS(fstS(fstS(fstS(fstS p))))))))= p1) 
    by (replace p with {bool2bset p1,bool2bset p2,bool2bset o1,bool2bset o2,bool2bset o3,save,rb,fail,z}; destruct p1; easy).
assert (X2: fbset2bool (sndS(fstS(fstS(fstS(fstS(fstS(fstS(fstS p))))))))= p2) 
    by (replace p with {bool2bset p1,bool2bset p2,bool2bset o1,bool2bset o2,bool2bset o3,save,rb,fail,z}; destruct p2; easy).
assert (X3: fbset2bool (sndS(fstS(fstS(fstS(fstS(fstS(fstS p)))))))= o1) 
    by (replace p with {bool2bset p1,bool2bset p2,bool2bset o1,bool2bset o2,bool2bset o3,save,rb,fail,z}; destruct o1; easy).
assert (X4: fbset2bool (sndS(fstS(fstS(fstS(fstS(fstS p))))))= o2) 
    by (replace p with {bool2bset p1,bool2bset p2,bool2bset o1,bool2bset o2,bool2bset o3,save,rb,fail,z}; destruct o2; easy).
assert (X5: fbset2bool (sndS(fstS(fstS(fstS(fstS p)))))= o3) 
    by (replace p with {bool2bset p1,bool2bset p2,bool2bset o1,bool2bset o2,bool2bset o3,save,rb,fail,z}; destruct o3; easy).
rewrite <- X1 in H. rewrite <- X2 in H. rewrite <- X3 in H. rewrite <- X4 in H. rewrite <- X5 in H. 
apply step_ob_ibf_R in H; try CheckPure.
simpl fst in H. simpl snd in H.
replace p with {bool2bset p1,bool2bset p2,bool2bset o1,
                bool2bset o2,bool2bset o3,save,rb,fail,z} in H. 2: easy.
simpl fstS in H. simpl sndS in H.
repeat rewrite rew_fbset2bool in H.
destruct H as [H [H1 | [H1|[H1|H1]]]]; split; try easy. 
- exists true true; easy.
- exists false true; easy.
- exists true false; easy.
- exists false false; easy.
Qed. 


(* ####################################################### *)
(** *     Output Buffer Bank Properties                    *)
(**  Only these properties are used outside                *)
(**  By induction on the type (of the primary outputs)     *)
(* ####################################################### *)

(** Property on the reshuffling plugs used to define       *)
(** output buffers                                         *)

Lemma fact_plug1_OB : forall S1 S2 S3 S4 S5 S6 s1 s2 s3 s4 s5 s6 t c, 
                      step (plug1_OB S1 S2 S3 S4 S5 S6) {s1, s2,{s3, s4, s5,s6}} t c
                   -> t={s2,s1,{s3,s4,s5,s6},{s3,s4,s6}} /\ c= plug1_OB S1 S2 S3 S4 S5 S6.
Proof.
introv H. unfold plug1_OB in H.
Invstep H. SimpS. eauto.
Qed.

Lemma fact_plug2_OB : forall S1 S2 S3 S4 S5 s1 s2 s3 s4 s5 t c, 
                      step (plug2_OB S1 S2 S3 S4 S5) {s1, {s2, s3},{s4, s5}} t c
                   -> t={s2,{s1,{s4,s3,s5}}} /\ c= plug2_OB S1 S2 S3 S4 S5.
Proof.
introv H. unfold plug2_OB in H.
Invstep H. SimpS. eauto.
Qed.

Lemma fact_plug3_OB : forall S1 S2 S3 S4 S5 S6 S7 s1 s2 s3 s4 s5 s6 s7 t c, 
                      step (plug3_OB S1 S2 S3 S4 S5 S6 S7) {s1, {s2,s3}, {s4,{s5,s6},s7}} t c
                   -> t={{s1,s4},{{s2,s5},{s3,s6}},s7} /\ c= plug3_OB S1 S2 S3 S4 S5 S6 S7.
Proof.
introv H. unfold plug3_OB in H.
Invstep H. SimpS. eauto.
Qed. 


(** The save and fail signals may be corrupted; roolBack=0, subst=0 *)

Lemma step_obs_sf : forall S (p p' o o' o'' s :{|S|}) save fail  t c, 
                       pure_bset {p,p',o,o',o'',s}
                    -> step (dtrOB_T p p' o o' o'') {s,{save,~0,fail,~0}} t c 
                    -> t={{p',{o',o''}},orS {fail,(bool2bset (negb (beq_buset_t o o')))}} 
                    /\ c=dtrOB_T s p s o o'.
Proof. 
induction S; introv P H.
- cbn in H. SimpS.
  assert (X1: exists b,  bool2bset b = s) by (apply pure_imp_exbool; easy).
  destruct X1 as [b X1]. subst.
  Apply step_ob_sf in H. 
  rewrite (b2bs_equiv_fb2bs H5) in H.
  rewrite (b2bs_equiv_fb2bs H3) in H.
  rewrite (b2bs_equiv_fb2bs H2) in H.
  replace (orS {fail, bool2bset (xorb (fbset2bool o) (fbset2bool o'))})
  with (orS {fail, bool2bset (negb (beq_buset_t o o'))}) in H.
  destruct H. easy. 
  Destruct_s o; destruct x2; Inverts H4; 
  Destruct_s o'; destruct x2; Inverts H3; 
  try easy.
- Dd_buset_all. cbn in H. Invstep H.
  apply fact_plug1_OB in H.  apply fact_plug2_OB in H3.
  apply fact_plug3_OB in H2. SimpS.
  Apply IHS1 in H7. SimpS.
  Apply IHS2 in H4. SimpS. cbn.
  Destruct_s fail; destruct x; destruct (beq_buset_t x50 x48); 
  destruct (beq_buset_t x51 x49); easy.
Qed.


(** The input, fail and save signals may be corrupted; roolBack=0, subst=0 *)

Lemma step_obs_ibf : forall S (p p' o o' o'' s :{|S|}) fail save t c, 
                     pure_bset {p,p',o,o',o'',save}
                  -> step (dtrOB_T p p' o o' o'') {s,{save,~0,fail,~0}} t c 
                  -> t={{p',{o',o''}},orS {fail,(bool2bset (negb (beq_buset_t o o')))}} 
                  /\ (exists y z, pure_bset y /\ pure_bset z /\ c=dtrOB_T y p z o o').
Proof.
induction S; introv P H.
- cbn in H. 
  Destruct_s s; destruct x; SimpS.
  + Apply step_ob_ibf in H. SimpS.
    repeat (rewrite rew_bool2bsetf); try easy.
    split.
    * Destruct_s fail; destruct x; Destruct_s o; 
      destruct x; Destruct_s o'; destruct x; try (Inverts H3); 
      try (Inverts H4); try easy. 
    * exists (bool2bset x) (bool2bset x0). 
      split. CheckPure. split. CheckPure.
      unfold dtrOB_T. repeat rewrite rew_fbset2bool; try easy. 
  + Apply step_ob_ibf in H. SimpS.
    repeat (rewrite rew_bool2bsetf); try easy.
    split.
    * Destruct_s fail; destruct x; Destruct_s o; 
      destruct x; Destruct_s o'; destruct x; try (Inverts H3); 
      try (Inverts H4); try easy. 
    * exists (bool2bset x) (bool2bset x0). 
      split. CheckPure. split. CheckPure.
      unfold dtrOB_T. repeat rewrite rew_fbset2bool; try easy. 
  + Apply step_ob_ibf in H. SimpS.
    repeat (rewrite rew_bool2bsetf); try easy. split. 
    * Destruct_s fail; destruct x; Destruct_s o; 
      destruct x; Destruct_s o'; destruct x; try (Inverts H3); 
      try (Inverts H4); try easy. 
    * exists (bool2bset x) (bool2bset x0).
      split. CheckPure. split. CheckPure.
      unfold dtrOB_T.  
      repeat (rewrite rew_fbset2bool). easy.
- Dd_buset_all. cbn in H. Invstep H.
  SimpS. apply fact_plug1_OB in H. SimpS.
  apply fact_plug2_OB in H3. SimpS.
  apply fact_plug3_OB in H2. SimpS.
  Apply IHS1 in H7. SimpS.
  Apply IHS2 in H4. SimpS.
  split.
  + cbn. Destruct_s fail; destruct x3; destruct (beq_buset_t x50 x48);
    destruct (beq_buset_t x51 x49); try easy.
  + exists {x,x1} {x0,x2}. easy.
Qed.
