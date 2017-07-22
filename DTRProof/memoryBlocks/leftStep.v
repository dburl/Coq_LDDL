(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-   Properties of mem block sub-part called lhsPar

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)
Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".
(*	Require Import CirReflect .*)
Require Import dtrTransform.

Set Implicit Arguments.

(* ##################################################################### *)
(** Properties of sub-circuit of Memory Block called lhsPar w/o Glitches *)
(* ##################################################################### *)

(* State before/after for both cycles w/o errors *)
(* by reflexion *)
Lemma step_lhs_R : forall p t c, ((fun p => pure_bset p) p) -> 
                           step ((fun p => 
                                     let d'_I :=   (sndS(fstS p)) in
                                     let r'_I :=   (sndS p) in
                                     let d' :=  fbset2bool d'_I in
                                     let r' :=  fbset2bool r'_I in

                                    lhsPar r' d') p)                        
                                ((fun p => 
                                     let dO_I :=   (sndS(fstS(fstS(fstS(fstS (fstS p)))))) in
                                     let rO_I :=   (sndS(fstS(fstS(fstS(fstS p))))) in
                                     let sav_I :=  (sndS(fstS(fstS(fstS p)))) in
                                     let fai_I :=  (sndS(fstS(fstS p))) in
                                     let d'_I :=   (sndS(fstS p)) in
                                     let r'_I :=   (sndS p) in
                                     let rol_I:=   (fstS(fstS(fstS(fstS(fstS (fstS p)))))) in

                                     {{{sav_I, rol_I},fai_I}, {dO_I, rO_I}} ) p) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in

                                     let dO_I :=   (sndS(fstS(fstS(fstS(fstS (fstS p)))))) in
                                     let rO_I :=   (sndS(fstS(fstS(fstS(fstS p))))) in
                                     let sav_I :=  (sndS(fstS(fstS(fstS p)))) in
                                     let fai_I :=  (sndS(fstS(fstS p))) in
                                     let d'_I :=   (sndS(fstS p)) in
                                     let r'_I :=   (sndS p) in
                                     let rol_I:=   (fstS(fstS(fstS(fstS(fstS (fstS p)))))) in

                                     let d :=   fbset2bool dO_I in
                                     let r :=   fbset2bool rO_I  in
                                     let sav := fbset2bool sav_I in
                                     let fai := fbset2bool fai_I in
                                     let d' :=  fbset2bool d'_I in
                                     let r' :=  fbset2bool r'_I in
                                     let rol := fbset2bool rol_I in

                                     let  so_O  := if (eqb rol false) then (bool2bset d') 
                                                   else (if (eqb sav false) then bool2bset d 
                                                         else bool2bset r') in
                                     let  sav_O := bool2bset sav in
                                     let  rol_O := bool2bset rol in
                                     let  fai_O :=  bool2bset (orb (negb (eqb d' d)) fai) in
                                     let  rO_O := bool2bset r in
                                     let  sav2_O := bool2bset sav in

  t={{so_O, {{sav_O, rol_O},fai_O}}, {rO_O, sav2_O}}/\ 
 (c= lhsPar (if (eqb sav false) then r' else r) d)) (p,t,c).
Proof. introv. Reflect_step_g. Qed.

(** The aforementioned property in a more useable form  *)
Lemma step_lhs:  forall (d r d' r' sav rol fai:bool) sav_I rol_I fai_I dO_I  rO_I t lhs2,
      step (lhsPar r' d') {{{sav_I, rol_I},fai_I}, {dO_I, rO_I}} t lhs2
     -> dO_I =  bool2bset d -> rO_I= bool2bset r -> sav_I= bool2bset sav ->  rol_I =  bool2bset rol -> fai_I =  bool2bset fai
     -> 
        let so_O := if (eqb rol false) then (bool2bset d') 
                    else (if (eqb sav false) then bool2bset d 
                          else bool2bset r') in
        let  sav_O := bool2bset sav in
        let  rol_O := bool2bset rol in
        let  fai_O :=  bool2bset (orb (negb (eqb d' d)) fai) in
        let  rO_O := bool2bset r in
        let  sav2_O := bool2bset sav in

        t={{so_O, {{sav_O, rol_O},fai_O}}, {rO_O, sav2_O}} /\ lhs2 = lhsPar (if (eqb sav false) then r' else r) d.
Proof.
introv H G1 G2 G3 G4 G5. set (p := {bool2bset rol, bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}).
assert (X0: rol_I= (fstS(fstS(fstS(fstS(fstS (fstS p))))))) by
(replace p with {bool2bset rol, bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct rol ; easy).
assert (X1: dO_I= (sndS(fstS(fstS(fstS(fstS (fstS p))))))) by
(replace p with {bool2bset rol, bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct d ; easy).
assert (X2: rO_I =   (sndS(fstS(fstS(fstS(fstS p)))))) by
(replace p with {bool2bset rol, bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct r ; easy).
assert (X3: sav_I =  (sndS(fstS(fstS(fstS p))))) by
(replace p with {bool2bset rol, bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct sav ; easy).
assert (X4: fai_I =  (sndS(fstS(fstS p)))) by
(replace p with {bool2bset rol, bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct fai ; easy).
assert (X5: d' =  fbset2bool (sndS(fstS p))) by
(replace p with {bool2bset rol, bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct d' ; easy).
assert (X6: r' = fbset2bool  (sndS p)) by
(replace p with {bool2bset rol, bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct r' ; easy).
rewrite X0 in H. rewrite X1 in H. rewrite  X2 in H. rewrite  X3 in H. rewrite  X4 in H. rewrite X5 in H. rewrite  X6 in H.
Apply step_lhs_R in H. simpl fst in H. simpl snd in H.
rewrite <- X0 in H. rewrite <- X1 in H. rewrite <- X2 in H. rewrite <- X3 in H.
rewrite <- X4 in H. rewrite <- X5 in H. rewrite <- X6 in H.
rewrite  G3 in H. rewrite G4 in H. rewrite  G1 in H. rewrite G2 in H. rewrite G5 in H.
rewrite rew_fbset2bool in H. rewrite rew_fbset2bool in H.
rewrite rew_fbset2bool in H. rewrite rew_fbset2bool in H.
rewrite rew_fbset2bool in H. apply H. 
Qed. 