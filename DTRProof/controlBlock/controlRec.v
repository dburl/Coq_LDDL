(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-   recovery process of ctr block and its properties 
          Dmitry Burlyaev - Pascal Fradet - 2015  
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)
(*
Add LoadPath "..\..\Common\".
Require Import CirReflect . 
Add LoadPath "..\..\TMRProof\".
Require Import tmrMainTh.
Add LoadPath "..\".
Require Import dtrTransform.
Add LoadPath "..\memoryBlocks".
*)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".
Add LoadPath "..\memoryBlocks\".

Require Import dtrTransform controlFsmStep.

Set Implicit Arguments.

(* ########################################################## *)
(** Properties of DTR control block during the recovery proces*)
(* ########################################################## *)

(*Recovery from internal control block corruption during the overal recovery:
if one of tree redundant parts of the control block is corrupted then 
the error disappears the next clock cycle thanks to TMR*)
Lemma stepr2_tcbv_C: forall fI t ctrTMR c,
                     pure_bset fI
                  -> corrupt_1in3_cir (ctrBl_dtr false true false) ctrTMR
                  -> step (ctrTMR -o- ctrVoting)  {fI,fI,fI}  t  c
                  -> t={~0,~1,~1,~1,~1} /\ c=(ctrBlockTMR false true true).
Proof.
introv H H0 H1. unfold ctrBlockTMR. split; Inverts H1.
 - apply tmr_corruptc  with (c':=(ctrBl_dtr false true true)) (s:=fI) (t:={~0,~1,~1,~1,~1}) in H0.
   + apply  det_step_res with (c1:=c1') (t1:=t0 )  in H0. Inverts H0.
     * assert (F:  fstep ctrVoting { ~ 0, ~ 1, ~ 1, ~ 1, ~ 1, 
                                   { ~ 0, ~ 1, ~ 1, ~ 1, ~ 1}, 
                                   { ~ 0, ~ 1, ~ 1, ~ 1, ~ 1}}  =   
                            Some ( { ~ 0, ~ 1, ~ 1, ~ 1, ~ 1} ,  ctrVoting)) by
       (vm_compute; try easy). eapply fstep_imp_detstep in F; Simpl.
     * apply H6.
   + Checkpure.
   + assert ( exists t, exists c', step (ctrBl_dtr false true false) fI t c' ). apply step_all_ex.
     Simpl. assert (HA :=  H1). apply fact_stepCtrBl_34 in H1. destruct H1; Simpl. 
 -apply tmr_corruptc  with (c':=(ctrBl_dtr  false true true)) (s:=fI) (t:={  ~ 0, ~ 1, ~ 1, ~ 1, ~ 1}) in H0.
   + apply  det_step_cod with (c1:=c1') (t1:=t0 )  in H0. Inverts H0.
      * apply step_comb_cir in H11; Simpl. repeat constructor.
      * Checkpure.
      * apply H6.
   + Checkpure.
   + assert ( exists t, exists c', step (ctrBl_dtr false true false) fI t c' ). apply step_all_ex.
     Simpl. assert (HA :=  H1). apply fact_stepCtrBl_34 in H1. destruct H1; Simpl.
Qed.

(*Property of control block: state transition during the recovery process: '010'-> '011'*)
(*by reflection*)
Lemma stepr2_tcbv_R : forall p t c, ((fun p => pure_bset p) p) -> 
                            step ((fun p => (ctrBlockTMR  false true false)) p)                        
                                 ((fun p => 
                                     let f3_I :=   (fstS(fstS p)) in
                                     let f2_I :=   (sndS(fstS p)) in
                                     let f1_I :=   (sndS p) in

                                     {f1_I, f2_I, f3_I} ) p) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in

                                t= {~0,~1,~1,~1,~1} /\ (c= (ctrBlockTMR  false true true))) (p,t,c).
Proof. introv. Reflect_step_g. Qed.

(** The aforementioned property in a more useable form  *)
Lemma stepr2_tcbv : forall (f1 f2 f3:bool) f1_I f2_I f3_I t c ,
f1_I =  bool2bset  f1 -> f2_I= bool2bset  f2 ->  f3_I= bool2bset f3
                      -> step (ctrBlockTMR   false true false) {f1_I, f2_I, f3_I} t c
                      -> t= {~0,~1,~1,~1,~1} /\ c = (ctrBlockTMR false true true).
Proof.
introv G1 G2 G3 H. set (p := {bool2bset f3, bool2bset f2,bool2bset f1}).
assert (X0: f1_I= (sndS p)) by
(replace p with {bool2bset f3, bool2bset f2,bool2bset f1}; destruct f1 ; easy).
assert (X1: f2_I= (sndS(fstS p)) ) by
(replace p with {bool2bset f3, bool2bset f2,bool2bset f1}; destruct f2 ; easy).
assert (X2: f3_I = (fstS(fstS p)) ) by
(replace p with {bool2bset f3, bool2bset f2,bool2bset f1}; destruct f3 ; easy).
rewrite X0 in H. rewrite X1 in H. rewrite  X2 in H. 
apply stepr2_tcbv_R with (t:=t) (c:=c) in H.
Simpl. CheckPure. 
Qed.

(*Property of control block: state transition during the recovery process: '011'-> '100'*)
(*by reflection*)
Lemma stepr3_tcbv_R : forall p t c, ((fun p => pure_bset p) p) -> 
                            step ((fun p =>(ctrBlockTMR   false true true)) p)                        
                                 ((fun p => 
                                     let f3_I :=   (fstS(fstS p)) in
                                     let f2_I :=   (sndS(fstS p)) in
                                     let f1_I :=   (sndS p) in

                                     {f1_I, f2_I, f3_I} ) p) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in

                                t=  {~0,~1,~0,~0,~1} /\ (c= (ctrBlockTMR   true false false))) (p,t,c).
Proof. introv. Reflect_step_g. Qed.

(** The aforementioned property in a more useable form  *)
Lemma stepr3_tcbv : forall (f1 f2 f3:bool) f1_I f2_I f3_I t c,
f1_I = bool2bset  f1 -> f2_I= bool2bset f2 ->  f3_I= bool2bset f3
                     -> step (ctrBlockTMR false true true) {f1_I, f2_I, f3_I} t c
                     -> t=  {~0,~1,~0,~0,~1} /\ c = (ctrBlockTMR  true false false).
Proof.
introv G1 G2 G3 H. set (p := {bool2bset f3, bool2bset f2,bool2bset f1}).
assert (X0: f1_I= (sndS p)) by
(replace p with {bool2bset f3, bool2bset f2,bool2bset f1}; destruct f1 ; easy).
assert (X1: f2_I= (sndS(fstS p)) ) by
(replace p with {bool2bset f3, bool2bset f2,bool2bset f1}; destruct f2 ; easy).
assert (X2: f3_I =   (fstS(fstS p)) ) by 
(replace p with {bool2bset f3, bool2bset f2,bool2bset f1}; destruct f3 ; easy).
rewrite X0 in H. rewrite X1 in H. rewrite  X2 in H. 
apply stepr3_tcbv_R with (t:=t) (c:=c) in H.
Simpl. CheckPure. 
Qed.

(*Property of control block: state transition during the recovery process: '100'-> '101'*)
(*by reflection*)
Lemma stepr4_tcbv_R : forall p t c, ((fun p => pure_bset p) p) -> 
                            step ((fun p =>(ctrBlockTMR   true false false)) p)                        
                                 ((fun p => 
                                     let f3_I :=   (fstS(fstS p)) in
                                     let f2_I :=   (sndS(fstS p)) in
                                     let f1_I :=   (sndS p) in

                                     {f1_I, f2_I, f3_I} ) p) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in

                               t=   {~0,~1,~0,~0,~0} /\ (c= (ctrBlockTMR   true false true))) (p,t,c).
Proof. introv. Reflect_step_g. Qed.

(** The aforementioned property in a more useable form  *)
Lemma  stepr4_tcbv : forall (f1 f2 f3:bool) f1_I f2_I f3_I t c ,
f1_I = bool2bset f1 -> f2_I= bool2bset f2 -> f3_I= bool2bset f3
                    -> step (ctrBlockTMR true false false) {f1_I, f2_I, f3_I} t c
                    -> t=  {~0,~1,~0,~0,~0} /\ c = (ctrBlockTMR   true false true).
Proof.
introv G1 G2 G3 H. set (p := {bool2bset f3, bool2bset f2,bool2bset f1}).
assert (X0: f1_I= (sndS p)) by
(replace p with {bool2bset f3, bool2bset f2,bool2bset f1}; destruct f1 ; easy).
assert (X1: f2_I= (sndS(fstS p))) by
(replace p with {bool2bset f3, bool2bset f2,bool2bset f1}; destruct f2 ; easy).
assert (X2: f3_I = (fstS(fstS p))) by
(replace p with {bool2bset f3, bool2bset f2,bool2bset f1}; destruct f3 ; easy).
rewrite X0 in H. rewrite X1 in H. rewrite  X2 in H. 
apply stepr4_tcbv_R with (t:=t) (c:=c) in H.
Simpl. CheckPure. 
Qed.

(*Property of control block: state transition during the recovery process: '101'-> '000'*)
(*by reflection*)
Lemma  stepr5_tcbv_R: forall p t c, ((fun p => pure_bset p) p) -> 
                            step ((fun p =>(ctrBlockTMR  true false true)) p)                        
                                 ((fun p => 
                                     let f3_I :=   (fstS(fstS p)) in
                                     let f2_I :=   (sndS(fstS p)) in
                                     let f1_I :=   (sndS p) in

                                     {f1_I, f2_I, f3_I} ) p) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in

                                t=    {~1,~0,~0,~0,~0} /\ (c= (ctrBlockTMR   false false false))) (p,t,c).
Proof. introv. Reflect_step_g. Qed.

(** The aforementioned property in a more useable form  *)
Lemma stepr5_tcbv   : forall (f1 f2 f3:bool) f1_I f2_I f3_I t c,
f1_I =  bool2bset  f1 -> f2_I= bool2bset  f2 ->  f3_I= bool2bset f3
                      -> step (ctrBlockTMR  true false true) {f1_I, f2_I, f3_I} t c
                      -> t= {~1,~0,~0,~0,~0} /\ c = (ctrBlockTMR  false false false).
Proof.
introv G1 G2 G3 H. set (p := {bool2bset f3, bool2bset f2,bool2bset f1}).
assert (X0: f1_I= (sndS p)) by
(replace p with {bool2bset f3, bool2bset f2,bool2bset f1}; destruct f1 ; easy).
assert (X1: f2_I= (sndS(fstS p))) by
(replace p with {bool2bset f3, bool2bset f2,bool2bset f1}; destruct f2 ; easy).
assert (X2: f3_I = (fstS(fstS p))) by
(replace p with {bool2bset f3, bool2bset f2,bool2bset f1}; destruct f3 ; easy).
rewrite X0 in H. rewrite X1 in H. rewrite  X2 in H. 
apply stepr5_tcbv_R with (t:=t) (c:=c) in H.
Simpl. CheckPure. 
Qed.