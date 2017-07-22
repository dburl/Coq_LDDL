(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
--   Properties of mem block sub-part called rhsPar with stepg

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)
(*Add LoadPath "..\..\Common\".
        Require Import CirReflect . 
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\". *)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import dtrTransform.

Set Implicit Arguments.

(* ###################################################################### *)
(** Properties of sub-circuit of Memory Block called rhsPar with Glitches *)
(* ###################################################################### *)

(* Type of rhsPar (IO interface):
  ((si1 # ({save#rollBack} # failF)) # (r_O # save)) -> 
  ( [((save # rollBack) # failF) # s1 ]# rNew)
*)

(* State before/after for both cycles with a glitch (stepg) inside the circuit *)
(*by reflexion*)
Lemma stepg_rhs_R : forall p t c, ((fun p => pure_bset p) p)
                  -> stepg ((fun p => 
                                     let si_I :=   (fstS(fstS(fstS(fstS(fstS p))))) in 
                                     let sav_I :=   (sndS(fstS(fstS(fstS(fstS p))))) in
                                     let sav2_I :=  (sndS(fstS(fstS(fstS p)))) in 
                                     let fai_I :=  (sndS(fstS(fstS p))) in 
                                     let rol_I :=   (sndS(fstS p)) in 
                                     let rO_I :=   (sndS p) in

                                     rhsPar) p)
                           ((fun p =>
                                     let si_I :=   (fstS(fstS(fstS(fstS(fstS p))))) in 
                                     let sav_I :=   (sndS(fstS(fstS(fstS(fstS p))))) in
                                     let sav2_I :=  (sndS(fstS(fstS(fstS p)))) in 
                                     let fai_I :=  (sndS(fstS(fstS p))) in 
                                     let rol_I :=   (sndS(fstS p)) in  
                                     let rO_I :=   (sndS p) in

                                   {si_I,{{{ sav_I, rol_I},fai_I},{rO_I,sav2_I}}}) p) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in

                               let si_I :=   (fstS(fstS(fstS(fstS(fstS p))))) in 
                               let sav_I :=   (sndS(fstS(fstS(fstS(fstS p))))) in
                               let sav2_I :=  (sndS(fstS(fstS(fstS p)))) in 
                               let fai_I :=  (sndS(fstS(fstS p))) in 
                               let rol_I :=   (sndS(fstS p)) in 
                               let rO_I :=   (sndS p) in 

                               let rI_I:=  if (beq_buset_t sav2_I (~1)) then si_I 
                                           else rO_I in

((c=rhsPar)/\ ( t= {{ {{sav_I,rol_I}, fai_I}, si_I}, rI_I} 
\/ t= {{ {{sav_I,rol_I}, fai_I}, si_I},~?}))) (p,t,c).
Proof. introv. Reflo_step_g; Simpl. Qed.

(** The aforementioned property in a more useable form  *)
Lemma stepg_rhs: forall (si sav sav2 fai rol r :bool) si_I sav_I  sav2_I fai_I rol_I rO_I t c,
si_I =  bool2bset si -> sav_I  = bool2bset sav -> sav2_I =  bool2bset sav2 -> 
fai_I  = bool2bset fai -> rol_I =  bool2bset rol ->  rO_I  = bool2bset r ->
stepg rhsPar  {si_I,{{{ sav_I, rol_I},fai_I},{rO_I,sav2_I}}} t c
->           
let rI_I:=  if (beq_buset_t sav2_I (~1)) then si_I else rO_I in                    
((c=rhsPar)/\ ( t= {{ {{sav_I,rol_I}, fai_I}, si_I}, rI_I} 
\/ t= {{ {{sav_I,rol_I}, fai_I}, si_I},~?})).
Proof.
introv G1 G2 G3 G4 G5 G6 H.
set (p := {bool2bset si, bool2bset sav, bool2bset sav2, bool2bset fai, bool2bset rol, bool2bset r}).
assert (X1:   si_I =   (fstS(fstS(fstS(fstS(fstS p)))))) by
(replace p with  {bool2bset si, bool2bset sav, bool2bset sav2, bool2bset fai, bool2bset rol, bool2bset r}; destruct si ; easy).
assert (X2:    sav_I =   (sndS(fstS(fstS(fstS(fstS p)))))) by
(replace p with  {bool2bset si, bool2bset sav, bool2bset sav2, bool2bset fai, bool2bset rol, bool2bset r}; destruct sav; easy).
assert (X3:    sav2_I =  (sndS(fstS(fstS(fstS p))))) by
(replace p with  {bool2bset si, bool2bset sav, bool2bset sav2, bool2bset fai, bool2bset rol, bool2bset r}; destruct sav2 ; easy).
assert (X4:    fai_I =  (sndS(fstS(fstS p)))) by
(replace p with  {bool2bset si, bool2bset sav, bool2bset sav2, bool2bset fai, bool2bset rol, bool2bset r}; destruct fai ; easy).
assert (X5:    rol_I =   (sndS(fstS p))) by
(replace p with  {bool2bset si, bool2bset sav, bool2bset sav2, bool2bset fai, bool2bset rol, bool2bset r}; destruct rol ; easy).
assert (X6:   rO_I =   (sndS p)) by
(replace p with  {bool2bset si, bool2bset sav, bool2bset sav2, bool2bset fai, bool2bset rol, bool2bset r}; destruct r ; easy).
intros. rewrite X1 in H. rewrite  X2 in H. rewrite  X3 in H.  rewrite X5 in H. rewrite  X6 in H.
rewrite X4 in H. Apply stepg_rhs_R in H. simpl fst in H. simpl snd in H.
rewrite <- X1 in H. rewrite <- X2 in H. rewrite <- X3 in H.
rewrite <- X5 in H. rewrite <- X6 in H.  rewrite <- X4 in H. apply H. 
Qed.