(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    Admitted
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
(** **     Properties of an output buffer                  *)
(* ####################################################### *)

(** **              Recovery mode               *) 

(* cycle 1 after error detection : save=1, roolBack=1, subst=1  *)    

Lemma stepr1_ob : forall p1 p2 o1 o2 o3 a fail t c, 
                     step (outBufDTR p1 p2 o1 o2 o3) {bool2bset a,{~1,~1,bool2bset fail,~1}} t c 
                  -> t={{bool2bset a,{bool2bset a,bool2bset a}},bool2bset(orb fail (negb(eqb o1 o2)))}
                  /\ c=outBufDTR a p1 a o1 o2.
Proof. 
introv H.
assert (F:fstep (outBufDTR p1 p2 o1 o2 o3) {bool2bset a,{~1,~1,bool2bset fail,~1}}  
        = Some ({{bool2bset a,{bool2bset a,bool2bset a}},bool2bset(orb fail (negb(eqb o1 o2)))},
                outBufDTR a p1 a o1 o2))
    by (destruct p1; destruct p2; destruct o1; destruct o2; destruct o3; destruct a; destruct fail; vm_compute; easy).
eapply fstep_imp_detstep in F; Simpl.
Qed.  

(* cycles 2 or 3 after error detection : save=0, roolBack=1, fail=0, subst=1  *)    

Lemma stepr23_ob : forall a1 a2 p2 o2 o3 fail t c, 
                    step (outBufDTR a1 p2 a1 o2 o3) {bool2bset a2,{~0,~1,bool2bset fail,~1}} t c 
                 -> t={{bool2bset a1,{bool2bset a1,bool2bset a1}},bool2bset(orb fail (negb(eqb a1 o2)))}
                  /\ c=outBufDTR a2 a1 a2 a1 o2.
Proof. 
introv H.
assert (F:fstep (outBufDTR a1 p2 a1 o2 o3) {bool2bset a2,{~0,~1,bool2bset fail,~1}}  
        = Some ({{bool2bset a1,{bool2bset a1,bool2bset a1}},bool2bset(orb fail (negb(eqb a1 o2)))},
                outBufDTR a2 a1 a2 a1 o2))
    by (destruct a1; destruct a2; destruct p2; destruct o2; destruct o3; destruct fail; vm_compute; try easy).
eapply fstep_imp_detstep in F; Simpl.  
Qed. 

(* cycle 4 after error detection : save=0, roolBack=1, fail=0, subst=0  *)    

Lemma stepr4_ob : forall a1 a2 a3 a4 f t c, 
                     step (outBufDTR a3 a2 a3 a2 a1) {bool2bset a4,{~0,~1,bool2bset f,~0}} t c 
                  -> t={{bool2bset a2,{bool2bset a2,bool2bset a1}},bool2bset(orb f (negb(eqb a3 a2)))}
                  /\ c=outBufDTR a4 a3 a4 a3 a2.
Proof.  
introv H.
assert (F:fstep (outBufDTR a3 a2 a3 a2 a1) {bool2bset a4,{~0,~1,bool2bset f,~0}}   
        = Some ({{bool2bset a2,{bool2bset a2,bool2bset a1}},bool2bset(orb f (negb(eqb a3 a2)))},
                outBufDTR a4 a3 a4 a3 a2))
    by (destruct a1; destruct a2; destruct a3; destruct a4; destruct f; vm_compute; easy).
eapply fstep_imp_detstep in F; Simpl.  
Qed. 

(* cycle 5 after error detection : save=0, roolBack=1, fail=0, subst=1  *)    


Lemma stepr5_ob : forall a1 a2 a3 f t c, 
                    step (outBufDTR a3 a2 a3 a2 a1) {bool2bset a3,{~1,~0,bool2bset f,~0}} t c 
                 -> t={{bool2bset a2,{bool2bset a2,bool2bset a1}},bool2bset(orb f (xorb a3 a2))}
                  /\ c=outBufDTR a3 a3 a3 a3 a2.
Proof. 
introv H.
assert (F:fstep (outBufDTR a3 a2 a3 a2 a1) {bool2bset a3,{~1,~0,bool2bset f,~0}}   
        = Some ({{bool2bset a2,{bool2bset a2,bool2bset a1}},bool2bset(orb f(xorb a3 a2))},
                outBufDTR a3 a3 a3 a3 a2))
    by (destruct a1; destruct a2; destruct a3; destruct f; vm_compute; easy).
eapply fstep_imp_detstep in F; Simpl.  
Qed. 



(* ####################################################### *)
(** *     Output Buffer Bank Properties                     *)
(* ####################################################### *)


(** **              Recovery mode               *) 

(* cycle 1 after error detection : even cycle and save=1, roolBack=1, fail=0, subst=1  *)    

Lemma stepr1_obs : forall S (p1 p2 o1 o2 o3 s:{|S|}) f t c, 
                      pure_bset p1 -> pure_bset p2 -> pure_bset o1 -> pure_bset o2 
                   -> pure_bset o3 -> pure_bset f -> pure_bset s 
                   -> step (dtrOB_T p1 p2 o1 o2 o3) {s,{~1,~1,f,~1}} t c 
                   -> (exists f, t={{s,{s,s}},f})
                   /\ c=dtrOB_T s p1 s o1 o2.
Proof. 
induction S; introv P1 P2 P3 P4 P5 P6 P H. 
- cbn in H. 
  assert (H1: exists b,  bool2bset b = s) by (apply pure_imp_exbool; easy).
  destruct H1 as [b H1]. subst.
  assert (H1: f = bool2bset(fbset2bool f))
  by (Destruct_s f; destruct x; Inverts P6; try easy).
  rewrite H1 in H. clear H1.
  apply stepr1_ob in H; try easy. SimpS.
  split.
  + exists (bool2bset(orb (fbset2bool f) (negb(beq_buset_t o1 o2)))).
    Destruct_s o1; destruct x; Inverts P3; 
    Destruct_s o2; destruct x; Inverts P4; destruct b; try easy.
  + Destruct_s p1; destruct x; Inverts P1;  Destruct_s o1; destruct x; Inverts P3; 
    Destruct_s o2; destruct x; Inverts P4; destruct b; try easy.
- Dd_buset_all. cbn in H. 
  Invstep H. apply fact_plug1_OB in H.  apply fact_plug2_OB in H3.
  apply fact_plug3_OB in H2. Simpl. Rpure. 
  apply IHS1 in H7; try easy. Simpl.
  apply IHS2 in H4; try easy. Simpl. 
Qed. 

(* cycles 2 or 3 after error detection : odd cycle and save=0, roolBack=1, fail=0, subst=1  *)    

Lemma stepr23_obs : forall S (p1 p2 o1 o2 s:{|S|}) f t c, 
                      pure_bset p1 -> pure_bset p2 -> pure_bset o1 -> pure_bset o2 
                   -> pure_bset f -> pure_bset s 
                   -> step (dtrOB_T p1 p2 p1 o1 o2) {s,{~0,~1,f,~1}} t c 
                   -> (exists f, t={{p1,{p1,p1}},f})
                   /\ c=dtrOB_T s p1 s p1 o1.
Proof.  
induction S; introv P1 P2 P3 P4 P5 P H. 
- cbn in H. 
  assert (H1: exists b,  bool2bset b = s) by (apply pure_imp_exbool; easy).
  destruct H1 as [b H1]. subst.
  assert (H1: f = bool2bset(fbset2bool f))
  by (Destruct_s f; destruct x; Inverts P5; try easy).
  rewrite H1 in H. clear H1.
  apply stepr23_ob in H; try easy. Simpl.
  split.
  + exists (bool2bset(orb (fbset2bool f) (negb(beq_buset_t p1 o1)))).
    Destruct_s o1; destruct x; Inverts P3; 
    Destruct_s p1; destruct x; Inverts P1;  
    Destruct_s f; destruct x; Inverts P5;  destruct b; vm_compute; reflexivity.
  + Destruct_s p1; destruct x; Inverts P1; 
    Destruct_s o1; destruct x; Inverts P3; 
    destruct b; reflexivity.
- Dd_buset_all. cbn in H. 
  Invstep H. apply fact_plug1_OB in H.  apply fact_plug2_OB in H3.
  apply fact_plug3_OB in H2. Simpl. Rpure. 
  eapply IHS1 in H7; try easy. Simpl.
  apply IHS2 in H4; try easy. Simpl. 
Qed. 


(* cycle 4 after error detection : odd cycle and save=0, roolBack=1, fail=0, subst=0  *)    

Lemma stepr4_obs : forall S (p1 p2 p3 p4 :{|S|}) f t c, 
                      pure_bset {p1,p2,p3,p4}
                   -> step (dtrOB_T p3 p2 p3 p2 p1) {p4,{~0,~1,bool2bset f,~0}} t c 
                   -> t={{p2,{p2,p1}},bool2bset(orb f (negb(beq_buset_t p3 p2)))}
                   /\ c=dtrOB_T p4 p3 p4 p3 p2.
Proof.
induction S; introv P H. 
- SimpS. 
  assert (X1: exists b4,  bool2bset b4 = p4) by (apply pure_imp_exbool; easy).
  destruct X1 as [b X1]. subst.
  apply stepr4_ob in H; try easy. SimpS.
  split; Destruct_s p1; destruct x; Inverts H0; 
  Destruct_s p2; destruct x; Inverts H3;  
  Destruct_s p3; destruct x; Inverts H2; destruct b; easy. 
- Dd_buset_all. cbn in H. 
  Invstep H. apply fact_plug1_OB in H.  apply fact_plug2_OB in H3.
  apply fact_plug3_OB in H2. SimpS. 
  eapply IHS1 in H7; try easy. SimpS.
  cbn. rewrite negb_andb. rewrite orb_assoc.
  apply IHS2 in H4; try easy. Simpl.
Qed. 


Lemma stepr5_obs : forall S (p1 p2 p3 :{|S|}) f t c, 
                      pure_bset {p1,p2,p3}
                   -> step (dtrOB_T p3 p2 p3 p2 p1) {p3,{~1,~0,bool2bset f,~0}} t c 
                   -> t={{p2,{p2,p1}},bool2bset(orb f (negb(beq_buset_t p3 p2)))}
                   /\ c=dtrOB_T p3 p3 p3 p3 p2.
Proof.
induction S; introv P H. 
- cbn in H. SimpS.
  assert (X1: exists b,  bool2bset b = p3) by (apply pure_imp_exbool; easy).
  destruct X1 as [b X1]. subst. rewrite rew_fbset2bool in H. 
  apply stepr5_ob in H; try easy. SimpS.
  split; Destruct_s p1; destruct x; Inverts H0; 
  Destruct_s p2; destruct x; Inverts H2;  
  destruct b; try easy.
- Dd_buset_all. cbn in H. 
  Invstep H. apply fact_plug1_OB in H.  apply fact_plug2_OB in H3.
  apply fact_plug3_OB in H2. SimpS.  
  eapply IHS1 in H7; try easy. SimpS. cbn.
  rewrite negb_andb. rewrite orb_assoc.
  apply IHS2 in H4; try easy. Simpl.
Qed. 

