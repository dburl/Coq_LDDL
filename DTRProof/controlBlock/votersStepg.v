(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-   PropertieS of control block voting part.      

          Dmitry Burlyaev - Pascal Fradet - 2015          
      
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)
(* Add LoadPath "..\..\Common\".
	Require Import CirReflect. 
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\".
*)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import dtrTransform.

Set Implicit Arguments.

(* ############################################################ *)
(** *      Properties of voting sub-circuit in Control Block    *)
(* ############################################################ *)

(*supporting property for votInpGl0 by reflexion*)
Lemma votInpGl_r1 : forall p t c,
                     ((fun p => pure_bset (~0)) p)
                  -> step ((fun p =>  ctrVoting) p)
                          ((fun p =>
let p5 := (sndS p) in  
let p4 := (sndS(fstS p)) in  
let p3 := (sndS(fstS(fstS p))) in
let p2 := (sndS(fstS(fstS(fstS p)))) in
let p1 := (fstS(fstS(fstS(fstS p)))) in

 {~0, ~0, ~0, ~0, ~0, {~0, ~0, ~0, ~0, ~0}, {p1, p2, p3, p4, p5}} ) p ) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in                               
              ((   t={~0,~0,~0,~0,~0} )/\ (c= ctrVoting))) (p,t,c).
Proof. introv. Reflo_step_g. Qed.
(*supporting property for votInpGl0 by reflexion*)
Lemma votInpGl_r2 : forall p t c,
                     ((fun p => pure_bset (~0)) p)
                  -> step ((fun p =>  ctrVoting) p)
                          ((fun p =>
let p5 := (sndS p) in  
let p4 := (sndS(fstS p)) in  
let p3 := (sndS(fstS(fstS p))) in
let p2 := (sndS(fstS(fstS(fstS p)))) in
let p1 := (fstS(fstS(fstS(fstS p)))) in

 {~0, ~0, ~0, ~0, ~0, {p1, p2, p3, p4, p5}, {~0, ~0, ~0, ~0, ~0}} ) p ) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in                               
              ((   t={~0,~0,~0,~0,~0} )/\ (c= ctrVoting))) (p,t,c).
Proof. introv. Reflo_step_g. Qed.
(*supporting property for votInpGl0 by reflexion*)
Lemma votInpGl_r3 : forall p t c,
                     ((fun p => pure_bset (~0)) p)
                  -> step ((fun p =>  ctrVoting) p)
                          ((fun p =>
let p5 := (sndS p) in  
let p4 := (sndS(fstS p)) in  
let p3 := (sndS(fstS(fstS p))) in
let p2 := (sndS(fstS(fstS(fstS p)))) in
let p1 := (fstS(fstS(fstS(fstS p)))) in

 {p1, p2, p3, p4, p5, {~0, ~0, ~0, ~0, ~0}, {~0, ~0, ~0, ~0, ~0}} ) p ) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in                               
              ((   t={~0,~0,~0,~0,~0} )/\ (c= ctrVoting))) (p,t,c).
Proof. introv. Reflo_step_g. Qed.

(*Property of shuffling+voting ctrVoting (added after TMR control block): *)
(*1) If 2 of 3 redundant buses are zero-vectors, then the output bus after voting is zero-vector*)
(*2) since the shuffling+voting is combinatorial circtuit, after a cycle it does not change its state and still combin.*)
Lemma votInpGl0:
forall gl t c', 
step ctrVoting {~ 0, ~ 0, ~ 0, ~ 0, ~ 0, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}, gl} t c' \/
step ctrVoting {~ 0, ~ 0, ~ 0, ~ 0, ~ 0, gl, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}} t c' \/
step ctrVoting { gl, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}, {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}} t c' 
                                                                             -> t={~0,~0,~0,~0,~0} /\c'=ctrVoting.
Proof.
introv H. Destruct_s gl. Destruct_s x. Destruct_s x.
Destruct_s x. rename x into y3. set (p := {y3,y2,y1,y0,y}).
assert (X0: y= (sndS p)) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
assert (X1: y0= (sndS(fstS p))) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
assert (X2: y1= (sndS(fstS(fstS p)))) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
assert (X3: y2=  (sndS(fstS(fstS(fstS p))))) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
assert (X4: y3= (fstS(fstS(fstS(fstS p))))) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
rewrite X0 in H. rewrite X1 in H. rewrite  X2 in H. rewrite  X3 in H. rewrite  X4 in H.
destruct H as [H|[H|H]].
Apply votInpGl_r1 in H. Apply votInpGl_r2 in H. Apply votInpGl_r3 in H.
Qed.

(*supporting property for votInpGl1 by reflexion*)
Lemma votInpGl1_r1 : forall p t c,
                     ((fun p => pure_bset (~0)) p)
                  -> step ((fun p =>  ctrVoting) p)
                          ((fun p =>
let p5 := (sndS p) in  
let p4 := (sndS(fstS p)) in  
let p3 := (sndS(fstS(fstS p))) in
let p2 := (sndS(fstS(fstS(fstS p)))) in
let p1 := (fstS(fstS(fstS(fstS p)))) in

 {~1, ~0, ~0, ~0, ~0, {~1, ~0, ~0, ~0, ~0}, {p1, p2, p3, p4, p5}} ) p ) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in                               
              ((   t={~1,~0,~0,~0,~0} )/\ (c= ctrVoting))) (p,t,c).
Proof. introv. Reflo_step_g. Qed.
(*supporting property for votInpGl1 by reflexion*)
Lemma votInpGl1_r2 : forall p t c,
                     ((fun p => pure_bset (~0)) p)
                  -> step ((fun p =>  ctrVoting) p)
                          ((fun p =>
let p5 := (sndS p) in  
let p4 := (sndS(fstS p)) in  
let p3 := (sndS(fstS(fstS p))) in
let p2 := (sndS(fstS(fstS(fstS p)))) in
let p1 := (fstS(fstS(fstS(fstS p)))) in

 {~1, ~0, ~0, ~0, ~0, {p1, p2, p3, p4, p5}, {~1, ~0, ~0, ~0, ~0}} ) p ) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in                               
              ((   t={~1,~0,~0,~0,~0} )/\ (c= ctrVoting))) (p,t,c).
Proof. introv. Reflo_step_g. Qed.
(*supporting property for votInpGl1 by reflexion*)
Lemma votInpGl1_r3 : forall p t c,
                     ((fun p => pure_bset (~0)) p)
                  -> step ((fun p =>  ctrVoting) p)
                          ((fun p =>
let p5 := (sndS p) in  
let p4 := (sndS(fstS p)) in  
let p3 := (sndS(fstS(fstS p))) in
let p2 := (sndS(fstS(fstS(fstS p)))) in
let p1 := (fstS(fstS(fstS(fstS p)))) in

 {p1, p2, p3, p4, p5, {~1, ~0, ~0, ~0, ~0}, {~1, ~0, ~0, ~0, ~0}} ) p ) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in                               
              ((   t={~1,~0,~0,~0,~0} )/\ (c= ctrVoting))) (p,t,c).
Proof. introv. Reflo_step_g. Qed.

(*Property of shuffling+voting ctrVoting (added after TMR control block): *)
(*1) If 2 of 3 redundant buses are the same vectors, then the output bus equals to them*)
(*2) since the shuffling+voting is combinatorial circtuit, after a cycle it does not change its state and still combin.*)
Lemma votInpGl1:
forall gl t c', 
step ctrVoting {~ 1, ~ 0, ~ 0, ~ 0, ~ 0, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}, gl} t c' \/
step ctrVoting {~ 1, ~ 0, ~ 0, ~ 0, ~ 0, gl, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}} t c' \/
step ctrVoting { gl, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}, {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}} t c' 
                                                                             -> t={~1,~0,~0,~0,~0} /\c'=ctrVoting.
Proof.
introv H. Destruct_s gl. Destruct_s x. Destruct_s x.
Destruct_s x. rename x into y3. set (p := {y3,y2,y1,y0,y}).
assert (X0: y= (sndS p)) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
assert (X1: y0= (sndS(fstS p))) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
assert (X2: y1= (sndS(fstS(fstS p)))) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
assert (X3: y2=  (sndS(fstS(fstS(fstS p))))) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
assert (X4: y3= (fstS(fstS(fstS(fstS p))))) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
rewrite X0 in H. rewrite X1 in H. rewrite  X2 in H. rewrite  X3 in H. rewrite  X4 in H.
destruct H as [H|[H|H]].
Apply votInpGl1_r1 in H. Apply votInpGl1_r2 in H. Apply votInpGl1_r3 in H.
Qed.

(*supporting property for votInpGlRec by reflexion*)
Lemma votInpGlRec_r1 : forall p t c,
                     ((fun p => pure_bset (~0)) p)
                  -> step ((fun p =>  ctrVoting) p)
                          ((fun p =>
let p5 := (sndS p) in  
let p4 := (sndS(fstS p)) in  
let p3 := (sndS(fstS(fstS p))) in
let p2 := (sndS(fstS(fstS(fstS p)))) in
let p1 := (fstS(fstS(fstS(fstS p)))) in

 {~ 1, ~ 1, ~ 1, ~ 1, ~ 1, {~ 1, ~ 1, ~ 1, ~ 1, ~ 1}, {p1, p2, p3, p4, p5}} ) p ) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in                               
              ((   t={~ 1, ~ 1, ~ 1, ~ 1, ~ 1} )/\ (c= ctrVoting))) (p,t,c).
Proof. introv. Reflo_step_g. Qed.
(*supporting property for votInpGl1 by reflexion*)
Lemma votInpGlRec_r2 : forall p t c,
                     ((fun p => pure_bset (~0)) p)
                  -> step ((fun p =>  ctrVoting) p)
                          ((fun p =>
let p5 := (sndS p) in  
let p4 := (sndS(fstS p)) in  
let p3 := (sndS(fstS(fstS p))) in
let p2 := (sndS(fstS(fstS(fstS p)))) in
let p1 := (fstS(fstS(fstS(fstS p)))) in

 {~ 1, ~ 1, ~ 1, ~ 1, ~ 1, {p1, p2, p3, p4, p5}, {~ 1, ~ 1, ~ 1, ~ 1, ~ 1}} ) p ) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in                               
              ((   t={~ 1, ~ 1, ~ 1, ~ 1, ~ 1} )/\ (c= ctrVoting))) (p,t,c).
Proof. introv. Reflo_step_g. Qed.
(*supporting property for votInpGl1 by reflexion*)
Lemma votInpGlRec_r3 : forall p t c,
                     ((fun p => pure_bset (~0)) p)
                  -> step ((fun p =>  ctrVoting) p)
                          ((fun p =>
let p5 := (sndS p) in  
let p4 := (sndS(fstS p)) in  
let p3 := (sndS(fstS(fstS p))) in
let p2 := (sndS(fstS(fstS(fstS p)))) in
let p1 := (fstS(fstS(fstS(fstS p)))) in

 {p1, p2, p3, p4, p5, {~ 1, ~ 1, ~ 1, ~ 1, ~ 1}, {~ 1, ~ 1, ~ 1, ~ 1, ~ 1}} ) p ) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in                               
              ((   t={~ 1, ~ 1, ~ 1, ~ 1, ~ 1} )/\ (c= ctrVoting))) (p,t,c).
Proof. introv. Reflo_step_g. Qed.

(*Property of shuffling+voting ctrVoting (added after TMR control block): *)
(*1) If 2 of 3 redundant buses are the same vectors, then the output bus equals to them*)
(*2) since the shuffling+voting is combinatorial circtuit, after a cycle it does not change its state and still combin.*)
Lemma votInpGlRec:
forall gl t c', 
step ctrVoting {~ 1, ~ 1, ~ 1, ~ 1, ~ 1, {~ 1, ~ 1, ~ 1, ~ 1, ~ 1}, gl} t c' \/
step ctrVoting {~ 1, ~ 1, ~ 1, ~ 1, ~ 1, gl, {~ 1, ~ 1, ~ 1, ~ 1, ~ 1}} t c' \/
step ctrVoting { gl, {~ 1, ~ 1, ~ 1, ~ 1, ~ 1}, {~ 1, ~ 1, ~ 1, ~ 1, ~ 1}} t c' 
                                                                             -> t={~ 1, ~ 1, ~ 1, ~ 1, ~ 1} /\c'=ctrVoting.
Proof.
introv H. Destruct_s gl. Destruct_s x. Destruct_s x.
Destruct_s x. rename x into y3. set (p := {y3,y2,y1,y0,y}).
assert (X0: y= (sndS p)) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
assert (X1: y0= (sndS(fstS p))) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
assert (X2: y1= (sndS(fstS(fstS p)))) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
assert (X3: y2=  (sndS(fstS(fstS(fstS p))))) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
assert (X4: y3= (fstS(fstS(fstS(fstS p))))) by
 (replace p with {y3,y2,y1,y0,y}; cbn; easy; symmetry; easy).
rewrite X0 in H. rewrite X1 in H. rewrite  X2 in H. rewrite  X3 in H. rewrite  X4 in H.
destruct H as [H|[H|H]].
Apply votInpGlRec_r1 in H. Apply votInpGlRec_r2 in H. Apply votInpGlRec_r3 in H.
Qed.
 

(* ############################################################ *)
(** Properties of voting sub-circuit in Control Block with Glitch *)
(* ############################################################ *)

(*Property of shuffling+voting ctrVoting (added after TMR control block) with GLITCH : *)
(*when all three redundant buses are the same, a glitch (stepg) can lead only to a single corrupted output*)
(*by reflection*)
Lemma stepg0_vot_R : forall p t c,
                     ((fun p => pure_bset p) p)
                  -> stepg ((fun p =>    let dO_I :=   (fstS p) in    (*d=d'=r*)
                                         let rO_I :=   (fstS p) in    (*d=d'=r*)
                                         let d' := fbset2bool dO_I in (*d=d'=r*)
                                         let r':= fbset2bool (sndS p) in
                                  ctrVoting) p)
                           ((fun p => {~0, ~0, ~0, ~0, ~0, {~0, ~0, ~0, ~0, ~0}, {~0, ~0, ~0, ~0, ~0}} ) p ) t c
                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in                               
                               let dO_I :=   (fstS p) in    (*d=d'=r*)
                               let rO_I :=   (fstS p) in    (*d=d'=r*)
                               let d' := fbset2bool dO_I in (*d=d'=r*)
                               let r':= fbset2bool (sndS p) in
              ((   t={~0,~0,~0,~0,~0}
                \/ t={~?,~0,~0,~0,~0}
                \/ t={~0,~?,~0,~0,~0}
                \/ t={~0,~0,~?,~0,~0}
                \/ t={~0,~0,~0,~?,~0}
                \/ t={~0,~0,~0,~0,~?})/\ (c= ctrVoting))) (p,t,c).
Proof.  introv. Reflo_step_g. Qed.

(** The property in a more useable form  *)
Lemma stepg0_vot: forall ttt c2, stepg ctrVoting 
                                           {~ 0, ~ 0, ~ 0, ~ 0, ~ 0, 
                                           {~ 0, ~ 0, ~ 0, ~ 0, ~ 0},  
                                           {~ 0, ~ 0, ~ 0, ~ 0, ~ 0}} ttt c2 
             ->   (ttt={~0,~0,~0,~0,~0}
                \/ ttt={~?,~0,~0,~0,~0}
                \/ ttt={~0,~?,~0,~0,~0}
                \/ ttt={~0,~0,~?,~0,~0}
                \/ ttt={~0,~0,~0,~?,~0}
                \/ ttt={~0,~0,~0,~0,~?})/\ c2= ctrVoting.
Proof.
introv H. set ( p := {bool2bset true, bool2bset false}). 
eapply stepg0_vot_R  with (t:=ttt) (c:=c2) in H; Simpl.
Qed.

(*Property of shuffling+voting ctrVoting (added after TMR control block) with GLITCH : *)
(*when all three redundant buses are the same, a glitch (stepg) can lead only to a single corrupted output*)
(*by reflection*)
Lemma stepg1_vot_R : forall p t c,
                     ((fun p => pure_bset p) p)
                  -> stepg ((fun p => let dO_I :=   (fstS p) in    (*d=d'=r*)
                                      let rO_I :=   (fstS p) in    (*d=d'=r*)
                                      let d' := fbset2bool dO_I in (*d=d'=r*)
                                      let r':= fbset2bool (sndS p) in
                                     ctrVoting) p)
                           ((fun p => {~1, ~0, ~0, ~0, ~0, {~1, ~0, ~0, ~0, ~0}, {~1, ~0, ~0, ~0, ~0}} ) p ) t c
                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in
                               let dO_I :=   (fstS p) in    (*d=d'=r*)
                               let rO_I :=   (fstS p) in    (*d=d'=r*)
                               let d' := fbset2bool dO_I in (*d=d'=r*)
                               let r':= fbset2bool (sndS p) in
              ((   t={~1,~0,~0,~0,~0}
                \/ t={~?,~0,~0,~0,~0}
                \/ t={~1,~?,~0,~0,~0}
                \/ t={~1,~0,~?,~0,~0}
                \/ t={~1,~0,~0,~?,~0}
                \/ t={~1,~0,~0,~0,~?})/\ (c= ctrVoting))) (p,t,c).
Proof.  introv. Reflo_step_g. Qed.

(** The property in a more useable form  *)
Lemma stepg1_vot:
forall ttt c2, stepg ctrVoting
                            {~ 1, ~ 0, ~ 0, ~ 0, ~ 0, 
                            {~ 1, ~ 0, ~ 0, ~ 0, ~ 0},
                            {~ 1, ~ 0, ~ 0, ~ 0, ~ 0}} ttt c2 
                ->(ttt={~1,~0,~0,~0,~0}
                \/ ttt={~?,~0,~0,~0,~0}
                \/ ttt={~1,~?,~0,~0,~0}
                \/ ttt={~1,~0,~?,~0,~0}
                \/ ttt={~1,~0,~0,~?,~0}
                \/ ttt={~1,~0,~0,~0,~?})/\ c2=ctrVoting.
Proof.
introv H. set ( p := {bool2bset true, bool2bset false}).
eapply stepg1_vot_R  with (t:=ttt) (c:=c2) in H; Simpl.
Qed.