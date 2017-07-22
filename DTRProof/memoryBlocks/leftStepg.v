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
(*Require Import CirReflect .*)
Require Import dtrTransform .

Set Implicit Arguments.

(* ###################################################################### *)
(** Properties of sub-circuit of Memory Block called lhsPar with Glitches *)
(* ###################################################################### *)

(** State before/after for both cycles if d input is glitched *)
(* by reflexion *)
Lemma step_lhs_i_R : forall p t c, ((fun p => pure_bset p) p) ->           
                       step ((fun p =>
                                     let d'_I :=   (sndS(fstS p)) in 
                                     let r'_I :=   (sndS p) in
                                     let d' :=  fbset2bool d'_I in
                                     let r' :=  fbset2bool r'_I in

                                    lhsPar r' d') p)                        
                                ((fun p => 
                                     let rO_I :=   (sndS(fstS(fstS(fstS(fstS p))))) in
                                     let sav_I :=  (sndS(fstS(fstS(fstS p)))) in
                                     let fai_I :=  (sndS(fstS(fstS p))) in
                                     let rol_I:=   (fstS(fstS(fstS(fstS(fstS p))))) in 

                                    {{{sav_I, rol_I},fai_I}, {~?, rO_I}} ) p) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in

                               let dO_I :=  (~?) in
                               let rO_I :=   (sndS(fstS(fstS(fstS(fstS p))))) in
                               let sav_I :=  (sndS(fstS(fstS(fstS p)))) in
                               let fai_I :=  (sndS(fstS(fstS p))) in
                               let d'_I :=   (sndS(fstS p)) in
                               let r'_I :=   (sndS p) in
                               let rol_I:=   (fstS(fstS(fstS(fstS(fstS p))))) in 
                               let r :=   fbset2bool rO_I  in
                               let sav := fbset2bool sav_I in
                               let fai := fbset2bool fai_I in
                               let d' :=  fbset2bool d'_I in
                               let r' :=  fbset2bool r'_I in
                               let rol :=   fbset2bool rol_I in
                             
                               let  so_O  := if (eqb rol false) then  bool2bset d' 
                                             else if ((eqb rol true)&&((eqb sav true))) then bool2bset r'
                                                  else dO_I in
                               let  sav_O := bool2bset sav in
                               let  rol_O := rol_I in
                               let  localFail:= if (beq_buset_t dO_I (~?)) then (~?)
                                                else if ((beq_buset_t dO_I (~1))&&(eqb d' true)) then (~0)
                                                else if ((beq_buset_t dO_I (~0))&&(eqb d' false)) then (~0)
                                                else (~1) in
                               let  fai_O :=   (orS (Pset fai_I localFail) ) in
                               let  rO_O := bool2bset r in
                               let  sav2_O := bool2bset sav in

   t={{so_O, {{sav_O, rol_O},fai_O}}, {rO_O, sav2_O}}/\ (c=lhsPar (if eqb sav false then r' else r) true 
                                                     \/ c=lhsPar (if eqb sav false then r' else r) false)) (p,t,c).
Proof. 
introv. Reflect_step_g. Qed.

(** The aforementioned property in a more useable form  *)
Lemma step_lhs_i: forall (rol r d' r' sav fai:bool) sav_I fai_I rol_I  rO_I t c,
rol_I =  bool2bset rol -> rO_I= bool2bset r -> sav_I= bool2bset sav ->  fai_I =  bool2bset fai -> 
step (lhsPar r' d') {{{sav_I, rol_I},fai_I}, {~?, rO_I}} t c
-> let dO_I :=  (~?) in
   let  so_O  := if (eqb rol false) then  bool2bset d' 
                 else if ((eqb rol true)&&((eqb sav true))) then bool2bset r'
                 else dO_I in
                 let  sav_O := bool2bset sav in
                 let  rol_O :=  bool2bset rol in

   let  localFail:= if (beq_buset_t dO_I (~?)) then (~?)
                    else if ((beq_buset_t dO_I (~1))&&(eqb d' true)) then (~0)
                    else if ((beq_buset_t dO_I (~0))&&(eqb d' false)) then (~0)
                    else (~1) in
   let  fai_O :=   (orS (Pset (bool2bset fai) localFail) ) in
   let  rO_O := bool2bset r in
   let  sav2_O := bool2bset sav in

  t={{so_O, {{sav_O, rol_O},fai_O}}, {rO_O, sav2_O}} 
  /\ (c=lhsPar (if eqb sav false then r' else r) true 
   \/ c=lhsPar (if eqb sav false then r' else r) false).
Proof.
introv G1 G2 G3 G4 H. set (p := {bool2bset rol, bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}).
assert (X1:  rol_I =(fstS(fstS(fstS(fstS(fstS p)))))) by
(replace p with {bool2bset  rol,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct rol ; easy).
assert (X2:   rO_I= (sndS(fstS(fstS(fstS(fstS p)))))) by
(replace p with {bool2bset  rol,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct r ; easy).
assert (X3:   sav_I=(sndS(fstS(fstS(fstS p))))) by
(replace p with {bool2bset  rol,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct sav ; easy).
assert (X4:   fai_I= (sndS(fstS(fstS p)))) by
(replace p with {bool2bset  rol,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct fai ; easy).
assert (X5: d'=fbset2bool  (sndS(fstS p))) by
(replace p with {bool2bset  rol,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct d' ; easy).
assert (X6:  r'=fbset2bool  (sndS p)) by
(replace p with {bool2bset  rol,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct r' ; easy).
intros. rewrite X1 in H. rewrite  X2 in H. rewrite  X3 in H. rewrite  X4 in H. rewrite X5 in H. rewrite  X6 in H.
Apply step_lhs_i_R in H. simpl fst in H. simpl snd in H.
rewrite <- X1 in H. rewrite <- X2 in H. rewrite <- X3 in H.
rewrite <- X4 in H. rewrite <- X5 in H. rewrite <- X6 in H.
rewrite  G3 in H. rewrite G4 in H. rewrite  G1 in H. rewrite G2 in H.
rewrite rew_fbset2bool in H. rewrite rew_fbset2bool in H.
rewrite rew_fbset2bool in H.  apply H.
Qed.

(** Glitch on the input wire (fail) of the memory block*)
(* by reflection  p={p,p',o1,o2,o3,save} *)
Lemma step_lhs_f_R : forall p t c, ((fun p => pure_bset p) p)->           
                       step ((fun p =>
                                     let d'_I :=   (sndS(fstS p)) in
                                     let r'_I :=   (sndS p) in
                                     let d' :=  fbset2bool d'_I in
                                     let r' :=  fbset2bool r'_I in

                                     lhsPar r' d') p)                        
                                ((fun p => 
                                     let dO_I :=   (fstS(fstS(fstS(fstS(fstS p))))) in
                                     let rO_I :=   (sndS(fstS(fstS(fstS(fstS p))))) in
                                     let sav_I :=  (sndS(fstS(fstS(fstS p)))) in
                                     let rol_I :=  (sndS(fstS(fstS p))) in

                                    {{{sav_I, rol_I}, ~?}, {dO_I, rO_I}} ) p) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in

                               let dO_I :=   (fstS(fstS(fstS(fstS(fstS p))))) in
                               let rO_I :=   (sndS(fstS(fstS(fstS(fstS p))))) in
                               let sav_I :=  (sndS(fstS(fstS(fstS p)))) in
                               let fai_I :=   (~?) in
                               let d'_I :=   (sndS(fstS p)) in
                               let r'_I :=   (sndS p) in
                               let rol_I:=   (sndS(fstS(fstS p)))  in

                               let d :=   fbset2bool dO_I in
                               let r :=   fbset2bool rO_I  in
                               let sav := fbset2bool sav_I in
                               let rol := fbset2bool rol_I in
                               let d' :=  fbset2bool d'_I in
                               let r' :=  fbset2bool r'_I in

                               let so_O := if (eqb rol false) then (bool2bset d') 
                                           else (if (eqb sav false) then bool2bset d 
                                                 else bool2bset r') in
                               let  sav_O := bool2bset sav in
                               let  rol_O := bool2bset rol in
                               let  rO_O := bool2bset r in
                               let  sav2_O := bool2bset sav in
                               let  fai_O:= if negb (eqb d' d) then (~1) else (~?) in

    t={{so_O, {{sav_O, rol_O},fai_O}}, {rO_O, sav2_O}} 
         /\ (c=lhsPar (if eqb sav false then r' else r) d )) (p,t,c).
Proof. introv. Reflect_step_g. Qed.

(** The aforementioned property in a more useable form  *)
Lemma step_lhs_f: forall (d r d' r' sav rol:bool) sav_I rol_I dO_I  rO_I t lhs2,
dO_I =  bool2bset d -> rO_I= bool2bset r -> sav_I= bool2bset sav ->  rol_I =  bool2bset rol -> 
step (lhsPar r' d') {{{sav_I, rol_I },~?}, {dO_I, rO_I}} t lhs2
-> 
let so_O := if (eqb rol false) then (bool2bset d') 
            else (if (eqb sav false) then bool2bset d 
                  else bool2bset r') in
let  sav_O := bool2bset sav in
let  rol_O := bool2bset rol in
let  rO_O := bool2bset r in
let  sav2_O := bool2bset sav in
let  fai_O:= if negb (eqb d' d) then (~1) else (~?) in

t={ {so_O, {{sav_O, rol_O},fai_O}}, {rO_O, sav2_O}}/\ lhs2 = lhsPar(if (eqb sav false) then r' else r) d.
Proof.
introv G1 G2 G3 G4 H. set (p := {bool2bset d,bool2bset r,bool2bset sav,bool2bset rol,bool2bset d',bool2bset r'}).
assert (X1:  dO_I =(fstS(fstS(fstS(fstS(fstS p)))))) by
(replace p with {bool2bset d,bool2bset r,bool2bset sav,bool2bset rol,bool2bset d',bool2bset r'}; destruct d ; easy).
assert (X2:   rO_I= (sndS(fstS(fstS(fstS(fstS p)))))) by
(replace p with {bool2bset d,bool2bset r,bool2bset sav,bool2bset rol,bool2bset d',bool2bset r'}; destruct r ; easy).
assert (X3:   sav_I=(sndS(fstS(fstS(fstS p))))) by 
(replace p with {bool2bset d,bool2bset r,bool2bset sav,bool2bset rol,bool2bset d',bool2bset r'}; destruct sav ; easy).
 assert (X4:   rol_I= (sndS(fstS(fstS p)))) by
(replace p with {bool2bset d,bool2bset r,bool2bset sav,bool2bset rol,bool2bset d',bool2bset r'}; destruct rol ; easy).
assert (X5: d'=fbset2bool  (sndS(fstS p))) by
(replace p with {bool2bset d,bool2bset r,bool2bset sav,bool2bset rol,bool2bset d',bool2bset r'}; destruct d' ; easy).
assert (X6:  r'=fbset2bool  (sndS p)) by
(replace p with {bool2bset d,bool2bset r,bool2bset sav,bool2bset rol,bool2bset d',bool2bset r'}; destruct r' ; easy).
intros. rewrite X1 in H. rewrite  X2 in H. rewrite  X3 in H. rewrite  X4 in H. rewrite X5 in H. rewrite  X6 in H.
Apply step_lhs_f_R in H. simpl fst in H. simpl snd in H.
rewrite <- X1 in H. rewrite <- X2 in H. rewrite <- X3 in H.
rewrite <- X4 in H. rewrite <- X5 in H. rewrite <- X6 in H.
rewrite  G3 in H. rewrite G4 in H. rewrite  G1 in H. rewrite G2 in H.
rewrite rew_fbset2bool in H. rewrite rew_fbset2bool in H.
rewrite rew_fbset2bool in H. rewrite rew_fbset2bool in H.
apply H. Qed.

(** State before/after for both cycles if rO_I input is glitched *)
(* by reflexion *)
Lemma step_lhs_r_R : forall p t c, ((fun p => pure_bset p) p) ->           
                       step ((fun p =>
                                     let d'_I :=   (sndS(fstS p)) in
                                     let r'_I :=   (sndS p) in
                                     let d' :=  fbset2bool d'_I in
                                     let r' :=  fbset2bool r'_I in

                                     lhsPar r' d') p)                        
                               ((fun p => 
                                     let dO_I :=   (fstS(fstS(fstS(fstS(fstS p))))) in
                                     let sav_I :=  (sndS(fstS(fstS(fstS p)))) in
                                     let fai_I :=  (sndS(fstS(fstS p))) in
                                     let rol_I:=   (sndS(fstS(fstS(fstS(fstS p))))) in

                                    {{{sav_I, rol_I},fai_I}, {dO_I, ~?}} ) p) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in

                               let dO_I :=   (fstS(fstS(fstS(fstS(fstS p))))) in
                               let rO_I :=   (~?)  in
                               let sav_I :=  (sndS(fstS(fstS(fstS p)))) in
                               let fai_I :=  (sndS(fstS(fstS p))) in
                               let d'_I :=   (sndS(fstS p)) in
                               let r'_I :=   (sndS p) in 
                               let rol_I:=   (sndS(fstS(fstS(fstS(fstS p))))) in
                               let d :=   fbset2bool dO_I in
                               let sav := fbset2bool sav_I in
                               let fai := fbset2bool fai_I in
                               let d' :=  fbset2bool d'_I in
                               let r' :=  fbset2bool r'_I in
                               let rol :=   fbset2bool rol_I  in
                               
                               let  so_O  := if (eqb rol false) then (bool2bset d') 
                                             else (if (eqb sav false) then bool2bset d 
                                                   else bool2bset r') in
                               let  sav_O := bool2bset sav in
                               let  rol_O := rol_I in
                               let  fai_O :=  bool2bset (orb (negb (eqb d' d)) fai) in
                               let  rO_O := rO_I in
                               let  sav2_O := bool2bset sav in

   t={{so_O, {{sav_O, rol_O},fai_O}}, {rO_O, sav2_O}} 
                 /\ (c=lhsPar (if eqb sav false then r' else true) d 
                   \/c=lhsPar (if eqb sav false then r' else false) d)) (p,t,c).
Proof. 
introv. Reflect_step_g.
Qed.

(** The aforementioned property in a more useable form  *)
Lemma step_lhs_r: forall (d rol d' r' sav fai:bool) sav_I fai_I dO_I  rol_I t c,
dO_I =  bool2bset d -> rol_I= bool2bset rol -> sav_I= bool2bset sav ->  fai_I =  bool2bset fai -> 
step (lhsPar r' d') {{{sav_I, rol_I},fai_I}, {dO_I, ~?}} t c
-> 
  let rO_I :=   (~?)  in
  let  so_O  := if (eqb rol false) then (bool2bset d') 
                else (if (eqb sav false) then bool2bset d 
                      else bool2bset r') in
  let  sav_O := bool2bset sav in
  let  rol_O := bool2bset rol in
  let  fai_O :=  bool2bset (orb (negb (eqb d' d)) fai) in
  let  rO_O := rO_I in
  let  sav2_O := bool2bset sav in

  t={{so_O, {{sav_O, rol_O},fai_O}}, {rO_O, sav2_O}} 
               /\ (c=lhsPar (if eqb sav false then r' else true) d 
                 \/c=lhsPar (if eqb sav false then r' else false) d).
Proof.
introv G1 G2 G3 G4 H. set (p := {bool2bset d,bool2bset rol,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}).
assert (X1:  dO_I =(fstS(fstS(fstS(fstS(fstS p)))))) by
(replace p with {bool2bset d,bool2bset rol,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct d ; easy).
assert (X2:   rol_I= (sndS(fstS(fstS(fstS(fstS p)))))) by
(replace p with {bool2bset d,bool2bset rol,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct rol ; easy).
assert (X3:   sav_I=(sndS(fstS(fstS(fstS p))))) by
(replace p with {bool2bset d,bool2bset rol,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct sav ; easy).
assert (X4:   fai_I= (sndS(fstS(fstS p)))) by
(replace p with {bool2bset d,bool2bset rol,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct fai ; easy).
assert (X5: d'=fbset2bool  (sndS(fstS p))) by
(replace p with {bool2bset d,bool2bset rol,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct d' ; easy).
assert (X6:  r'=fbset2bool  (sndS p)) by
(replace p with {bool2bset d,bool2bset rol,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct r' ; easy).
intros. rewrite X1 in H. rewrite  X2 in H. rewrite  X3 in H. rewrite  X4 in H. rewrite X5 in H. rewrite  X6 in H.
Apply step_lhs_r_R in H. simpl fst in H. simpl snd in H.
rewrite <- X1 in H. rewrite <- X2 in H. rewrite <- X3 in H.
rewrite <- X4 in H. rewrite <- X5 in H. rewrite <- X6 in H.
rewrite  G3 in H. rewrite G4 in H. rewrite  G1 in H. rewrite G2 in H.
rewrite rew_fbset2bool in H. rewrite rew_fbset2bool in H.
rewrite rew_fbset2bool in H. rewrite rew_fbset2bool in H.
apply H. Qed.

(** State before/after for both cycles if save input is glitched *)
(* by reflexion *)
Lemma step_lhs_s_R : forall p t c, ((fun p => pure_bset p) p) ->           
                           step ((fun p =>
                                     let d'_I :=   (sndS(fstS p)) in
                                     let r'_I :=   (sndS p) in
                                     let d' :=  fbset2bool d'_I in
                                     let r' :=  fbset2bool r'_I in

                                     lhsPar r' d') p)                        
                                ((fun p => 
                                     let dO_I :=   (fstS(fstS(fstS(fstS(fstS p))))) in
                                     let rO_I :=   (sndS(fstS(fstS(fstS(fstS p))))) in
                                     let fai_I :=  (sndS(fstS(fstS p))) in
                                     let rol_I:=    (sndS(fstS(fstS(fstS p)))) in 

                                    {{{~? , rol_I},fai_I}, {dO_I, rO_I}} ) p) t c

                   -> (fun e => let p := fst(fst e) in 
                                let t := snd(fst e) in
                                let c := snd e in

                                let dO_I :=   (fstS(fstS(fstS(fstS(fstS p))))) in
                                let rO_I :=   (sndS(fstS(fstS(fstS(fstS p))))) in
                                let sav_I :=  (~?) in
                                let fai_I :=  (sndS(fstS(fstS p))) in
                                let d'_I :=   (sndS(fstS p)) in
                                let r'_I :=   (sndS p) in
                                let rol_I:=    (sndS(fstS(fstS(fstS p)))) in


                                let d :=   fbset2bool dO_I in
                                let r :=   fbset2bool rO_I  in
                                let fai := fbset2bool fai_I in
                                let d' :=  fbset2bool d'_I in
                                let r' :=  fbset2bool r'_I in
                                let rol := fbset2bool rol_I in
                                
                                let so_O := if (eqb rol false) then  bool2bset d' 
                                            else if ((eqb rol true)&&((beq_buset_t sav_I (~1))    )) then bool2bset r'
                                            else if ((eqb rol true)&&((beq_buset_t sav_I (~0))    )) then bool2bset d
                                            else if ((eqb rol true)&&((beq_buset_t sav_I (~?))&&(eqb r' false)&&(eqb d false)    )) then (~0)
                                            else  (~?)  in
                                let  sav_O := sav_I in
                                let  rol_O :=  bool2bset rol in
                                let  fai_O :=  bool2bset (orb (negb (eqb d' d)) fai) in
                                let  rO_O := bool2bset r in
                                let  sav2_O := sav_I in

  t={{so_O, {{sav_O, rol_O},fai_O}}, {rO_O, sav2_O}} /\ (c=lhsPar true  d \/ c=lhsPar false d)) (p,t,c).
Proof. 
introv. Reflect_step_g.
Qed.

(** The aforementioned property in a more useable form  *)
Lemma step_lhs_s: forall (d r d' r' rol fai:bool) rol_I fai_I dO_I  rO_I t c,
dO_I =  bool2bset d -> rO_I= bool2bset r -> rol_I= bool2bset rol ->  fai_I =  bool2bset fai -> 
step (lhsPar r' d') {{{~?, rol_I },fai_I}, {dO_I, rO_I}} t c
-> 
let sav_I :=  (~?) in
let so_O := if (eqb rol false) then  bool2bset d' 
            else if ((eqb rol true)&&((beq_buset_t sav_I (~1)))) then bool2bset r'
            else if ((eqb rol true)&&((beq_buset_t sav_I (~0)))) then bool2bset d
            else if ((eqb rol true)&&((beq_buset_t sav_I (~?))&&(eqb r' false)&&(eqb d false))) then (~0)
            else  (~?)  in
let  sav_O := sav_I in
let  rol_O :=  bool2bset rol in
let  fai_O :=  bool2bset (orb (negb (eqb d' d)) fai) in
let  rO_O := bool2bset r in
let  sav2_O := sav_I in

t={{so_O, {{sav_O, rol_O},fai_O}}, {rO_O, sav2_O}} /\ (c=lhsPar true  d \/ c=lhsPar false d).
Proof.
introv G1 G2 G3 G4 H. set (p := {bool2bset d,bool2bset r,bool2bset rol, bool2bset fai,bool2bset d',bool2bset r'}).
assert (X1:  dO_I =(fstS(fstS(fstS(fstS(fstS p)))))) by
(replace p with {bool2bset d,bool2bset r,bool2bset rol,bool2bset fai,bool2bset d',bool2bset r'}; destruct d ; easy).
assert (X2:   rO_I= (sndS(fstS(fstS(fstS(fstS p)))))) by
(replace p with {bool2bset d,bool2bset r,bool2bset rol,bool2bset fai,bool2bset d',bool2bset r'}; destruct r ; easy).
assert (X3:   rol_I=(sndS(fstS(fstS(fstS p))))) by
(replace p with {bool2bset d,bool2bset r,bool2bset rol,bool2bset fai,bool2bset d',bool2bset r'}; destruct rol ; easy).
assert (X4:   fai_I= (sndS(fstS(fstS p)))) by
(replace p with {bool2bset d,bool2bset r,bool2bset rol,bool2bset fai,bool2bset d',bool2bset r'}; destruct fai ; easy).
assert (X5: d'=fbset2bool  (sndS(fstS p))) by
(replace p with {bool2bset d,bool2bset r,bool2bset rol,bool2bset fai,bool2bset d',bool2bset r'}; destruct d' ; easy).
assert (X6:  r'=fbset2bool  (sndS p)) by
(replace p with {bool2bset d,bool2bset r,bool2bset rol,bool2bset fai,bool2bset d',bool2bset r'}; destruct r' ; easy).
intros. rewrite X1 in H. rewrite  X2 in H. rewrite  X3 in H. rewrite  X4 in H. rewrite X5 in H. rewrite  X6 in H.
Apply step_lhs_s_R in H. simpl fst in H. simpl snd in H.
rewrite <- X1 in H. rewrite <- X2 in H. rewrite <- X3 in H.
rewrite <- X4 in H. rewrite <- X5 in H. rewrite <- X6 in H.
rewrite  G3 in H. rewrite G4 in H. rewrite  G1 in H. rewrite G2 in H.
rewrite rew_fbset2bool in H. rewrite rew_fbset2bool in H.
rewrite rew_fbset2bool in H. rewrite rew_fbset2bool in H. apply H. 
Qed.


(** Glitch on the input wire (rollBack) of the memory block*)
(* by reflection *)
Lemma step_lhs_b_R : forall p t c, ((fun p => pure_bset p) p) ->          
                       step ((fun p =>
                                     let d'_I :=   (sndS(fstS p)) in 
                                     let r'_I :=   (sndS p) in
                                     let d' :=  fbset2bool d'_I in
                                     let r' :=  fbset2bool r'_I in

                                     lhsPar r' d') p)                        
                                ((fun p => 
                                     let dO_I :=   (fstS(fstS(fstS(fstS(fstS p))))) in
                                     let rO_I :=   (sndS(fstS(fstS(fstS(fstS p))))) in
                                     let sav_I :=  (sndS(fstS(fstS(fstS p)))) in
                                     let fai_I :=  (sndS(fstS(fstS p))) in
 
                                    {{{sav_I, ~?},fai_I}, {dO_I, rO_I}} ) p) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in

                               let dO_I :=   (fstS(fstS(fstS(fstS(fstS p))))) in
                               let rO_I :=   (sndS(fstS(fstS(fstS(fstS p))))) in
                               let sav_I :=  (sndS(fstS(fstS(fstS p)))) in
                               let fai_I :=  (sndS(fstS(fstS p))) in
                               let d'_I :=   (sndS(fstS p)) in
                               let r'_I :=   (sndS p) in
                               let rol_I:=   (~?) in

                               let d :=   fbset2bool dO_I in
                               let r :=   fbset2bool rO_I  in
                               let sav := fbset2bool sav_I in
                               let fai := fbset2bool fai_I in
                               let d' :=  fbset2bool d'_I in
                               let r' :=  fbset2bool r'_I in
                               
                               let  so_O  := if ((beq_buset_t rol_I (~?)) && (eqb d' false)&&
                                                (((eqb sav true)&&(eqb r' false))||((eqb sav false)
                                                &&(eqb d false))))  then (~0)
                                             else if ((beq_buset_t rol_I (~?)))  then (~?)
                                             else if (beq_buset_t rol_I (~0)) then (bool2bset d') 
                                             else (if (eqb sav false) then bool2bset d 
                                             else bool2bset r') in
                               let  sav_O := bool2bset sav in
                               let  rol_O := rol_I in
                               let  fai_O :=  bool2bset (orb (negb (eqb d' d)) fai) in
                               let  rO_O := bool2bset r in
                               let  sav2_O := bool2bset sav in

  t={{so_O, {{sav_O, rol_O},fai_O}}, {rO_O, sav2_O}} 
                            /\ (c=lhsPar (if eqb sav false then r' else r) d )) (p,t,c).
Proof.
introv. Reflect_step_g.
Qed.

(** The aforementioned property in a more useable form  *)
Lemma step_lhs_b: forall (d r d' r' sav fai:bool) sav_I fai_I dO_I  rO_I t  lhs2,
dO_I =  bool2bset d -> rO_I= bool2bset r -> sav_I= bool2bset sav ->  fai_I =  bool2bset fai -> 
step (lhsPar r' d') {{{sav_I, ~?},fai_I}, {dO_I, rO_I}} t lhs2
-> 
let so_O := if ((beq_buset_t (~?) (~?)) && (eqb d' false)&& 
               (((eqb sav true)&&(eqb r' false))||((eqb sav false)
               &&(eqb d false))))  then (~0)
           else if ((beq_buset_t (~?) (~?)))  then (~?)
           else if (beq_buset_t (~?) (~0)) then (bool2bset d') 
           else (if (eqb sav false) then bool2bset d 
           else bool2bset r') in
let  sav_O := bool2bset sav in
let  rol_O := ~? in
let  fai_O :=  bool2bset (orb (negb (eqb d' d)) fai) in
let  rO_O := bool2bset r in
let  sav2_O := bool2bset sav in

t={ {so_O, {{sav_O, rol_O},fai_O}}, {rO_O, sav2_O}}
/\ lhs2 = lhsPar (if (eqb sav false) then r' else r) d.
Proof.
introv G1 G2 G3 G4 H. set (p := {bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}).
assert (X1:  dO_I =(fstS(fstS(fstS(fstS(fstS p)))))) by
(replace p with {bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct d ; easy).
assert (X2:   rO_I= (sndS(fstS(fstS(fstS(fstS p)))))) by
(replace p with {bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct r ; easy).
assert (X3:   sav_I=(sndS(fstS(fstS(fstS p))))) by
(replace p with {bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct sav ; easy).
assert (X4:   fai_I= (sndS(fstS(fstS p)))) by
(replace p with {bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct fai ; easy).
assert (X5: d'=fbset2bool  (sndS(fstS p))) by
(replace p with {bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct d' ; easy).
assert (X6:  r'=fbset2bool  (sndS p)) by
(replace p with {bool2bset d,bool2bset r,bool2bset sav,bool2bset fai,bool2bset d',bool2bset r'}; destruct r' ; easy).
intros. rewrite X1 in H. rewrite  X2 in H. rewrite  X3 in H. rewrite  X4 in H. rewrite X5 in H. rewrite  X6 in H.
Apply step_lhs_b_R in H. simpl fst in H. simpl snd in H.
rewrite <- X1 in H. rewrite <- X2 in H. rewrite <- X3 in H.
rewrite <- X4 in H. rewrite <- X5 in H. rewrite <- X6 in H.
rewrite  G3 in H. rewrite G4 in H. rewrite  G1 in H. rewrite G2 in H.
rewrite rew_fbset2bool in H. rewrite rew_fbset2bool in H.
rewrite rew_fbset2bool in H. rewrite rew_fbset2bool in H. apply H. 
Qed.


(** State before/after for odd(0) cycles if a glitch occurs (stepg)*)
(* by reflexion *)
(*Memory block config. during odd cycles: (d, d',r ,r')= (b, b, b, a)*)
Lemma stepg0_lhs_R : forall p t c, ((fun p => pure_bset p) p)
                  -> stepg ((fun p => 
                                      let dO_I :=   (fstS p) in (*d=d'=r*)
                                      let rO_I :=   (fstS p) in(*d=d'=r*)

                                      let d' := fbset2bool dO_I in (*d=d'=r*)
                                      let r':= fbset2bool (sndS p) in
                                  lhsPar r' d') p)
                           ((fun p =>
                                      let dO_I :=   (fstS p) in (*d=d'=r*)
                                      let rO_I :=   (fstS p) in(*d=d'=r*)
                                   {{{~0, ~0},~0}, {dO_I, rO_I}}) p) t c

                  -> (fun e => let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e in

                               let dO_I :=   (fstS p) in (*d=d'=r*)
                               let rO_I :=   (fstS p) in(*d=d'=r*)

                               let d' := fbset2bool dO_I in (*d=d'=r*)
                               let r':= fbset2bool (sndS p) in
                          exists x,   (
   ((t= {{~?,{{~0, ~0},~0}}, {rO_I, ~0}}\/t= {{~?,{{~0, ~0},~?}}, {rO_I, ~0}}
   \/t= {{bool2bset d',  {{~0, ~0},~?}}, {rO_I, ~0}})/\ (c=lhsPar r' d'))  
  \/((t={{bool2bset d',   {{~0, ~0},~0}}, {rO_I, ~0}})/\(c=lhsPar x d')))) (p,t,c).
Proof. introv. Reflo_step_g. Qed.

(** The aforementioned property in a more useable form  *)
Lemma stepg0_lhs: forall (d r' :bool) dO_I  r'_O t c,
dO_I =  bool2bset d -> r'_O  = bool2bset r' -> 
let d':=d in
let rO_I :=dO_I in
stepg (lhsPar r' d') {{{~0, ~0},~0}, {rO_I, dO_I}} t c
->                     
exists x,
 (((t= {{~?,{{~0, ~0},~0}}, {rO_I, ~0}}\/t= {{~?,{{~0, ~0},~?}}, {rO_I, ~0}}
  \/t= {{bool2bset d',  {{~0, ~0},~?}}, {rO_I, ~0}})/\ (c=lhsPar r' d'))  
\/((t={{bool2bset d',   {{~0, ~0},~0}}, {rO_I, ~0}})/\ (c=lhsPar x d'))).
Proof.
introv G1 G2 H. set ( p := {bool2bset d, bool2bset r'}).
assert (X1:  dO_I  = (fstS p)) by
(replace p with {bool2bset d, bool2bset r'}; destruct d ; easy).
assert (X2:  r'_O =  (sndS p)) by
(replace p with {bool2bset d, bool2bset r'}; destruct r' ; easy).
assert (X3:  d  = fbset2bool (fstS p)) by
(replace p with {bool2bset d, bool2bset r'}; destruct d ; easy).
assert (X4:  r' =  fbset2bool (sndS p)) by
(replace p with {bool2bset d, bool2bset r'}; destruct r' ; easy).
rewrite  X1 in H. rewrite  X3 in H. rewrite  X4 in H.
Apply stepg0_lhs_R in H. simpl fst in H. simpl snd in H.
rewrite <- X1 in H. rewrite <- X2 in H. 
rewrite  G1 in H. rewrite  G2 in H. rewrite rew_fbset2bool in H.
rewrite rew_fbset2bool in H. rewrite G1. apply H. 
Qed.


(** State before/after for even(1) cycles if a glitch occurs (stepg)*)
(* by reflexion *)
(*Memory block config. during odd cycles: (d, d',r ,r')= (c, b, b, a)*)
Lemma stepg1_lhs_R : forall p t c,((fun p => pure_bset p) p)
                  -> stepg ((fun p => 
                                      let fai_I :=  (fstS(fstS(fstS p))) in (*some unknown pure non-restricted coming fail*)
                                      let dO_I :=   (sndS(fstS(fstS p))) in (*=c - new coming value*)
                                      let rO_I :=   (sndS(fstS p)) in       (*=r=d'*)
                                      let r'_I :=   (sndS p) in
 
                                      let d' := fbset2bool rO_I in   (* r=d' =b *)
                                      let r':=  fbset2bool r'_I in  (*value a*)
                                     lhsPar r' d') p)
                           ((fun p => (*   (((save # rollBack) # failI) # (d_O # r_O)) *)
                                      let fai_I :=  (fstS(fstS(fstS p))) in (*some unknown pure non-restricted coming fail*)
                                      let dO_I :=   (sndS(fstS(fstS p))) in (*=c - new coming value*)
                                      let rO_I :=   (sndS(fstS p)) in (*=r=d'*)

                                   {{{~1, ~0}, fai_I }, {dO_I, rO_I}}) p) t c

                  -> (fun e =>let p := fst(fst e) in 
                               let t := snd(fst e) in
                               let c := snd e     in

                               let fai_I :=  (fstS(fstS(fstS p))) in (*some unknown pure non-restricted coming fail*)
                               let dO_I :=   (sndS(fstS(fstS p))) in (*=c - new coming value*)
                               let rO_I :=   (sndS(fstS p)) in (*=r=d'*)
                               
                               let d'N := fbset2bool dO_I in (*d=d'=r*)
                               let r'N := fbset2bool rO_I in
exists x b,   (((t= { {rO_I,   {{~1, ~0}, bool2bset b}}, {rO_I, ~1}})/\(c=lhsPar x d'N) ) (*only recovery bit r' is corrupted*)
            \/(((t= {{~?,      {{~1, ~0}, bool2bset b}}, {rO_I, ~1}})  (*so =?*)
              \/(t= {{~?,      {{~1, ~0}, ~?}},          {rO_I, ~1}})  (*so and fail=?*)
              \/(t= {{rO_I,    {{~1, ~0}, ~?}},          {rO_I, ~1}}))  (*so and fail=?*)
              /\(c=lhsPar r'N d'N)))) (p,t,c).
Proof. introv. Reflo_step_g; Simpl. Qed.

(** The aforementioned property in a more useable form  *)
Lemma stepg1_lhs: forall (d r  r' fai:bool) r'_I fai_I dO_I  rO_I t  c,
fai_I =  bool2bset fai -> dO_I =  bool2bset d -> rO_I= bool2bset r -> r'_I= bool2bset r' ->  
let d' := r in (* r=d' *)
stepg (lhsPar r' d') {{{~1, ~0}, fai_I }, {dO_I, rO_I}} t c 
-> 
exists x b, 
  (((t= {{rO_I,  {{~1, ~0},bool2bset b}},  {rO_I, ~1}})/\(c=lhsPar x (fbset2bool dO_I)) ) (*only recovery bit r' is corrupted*)
\/(((t= {{~?,    {{~1, ~0},bool2bset b}}, {rO_I, ~1}})       (*so =?*)
  \/(t= {{~?,    {{~1, ~0}, ~?}},         {rO_I, ~1}})       (*so and fail=?*)
  \/(t= {{rO_I,  {{~1, ~0}, ~?}},         {rO_I, ~1}}))      (*so and fail=?*)
 /\ (c=lhsPar (fbset2bool rO_I) (fbset2bool dO_I)))).        (*rO_O =?*)
Proof.
introv G1 G2 G3 G4 H. set (p := {bool2bset fai, bool2bset d, bool2bset r, bool2bset r'}).
assert (X1:  fai_I =(fstS(fstS(fstS p)))) by
(replace p with {bool2bset fai, bool2bset d, bool2bset r, bool2bset r'}; destruct fai ; easy).
assert (X2:   dO_I=  (sndS(fstS(fstS p)))) by
(replace p with {bool2bset fai, bool2bset d, bool2bset r, bool2bset r'}; destruct d ; easy).
assert (X3:   rO_I=(sndS(fstS p))) by
(replace p with {bool2bset fai, bool2bset d, bool2bset r, bool2bset r'}; destruct r ; easy).
assert (X4:   r'_I= (sndS p)) by
(replace p with {bool2bset fai, bool2bset d, bool2bset r, bool2bset r'}; destruct r' ; easy).
assert (X5: r=fbset2bool  rO_I). rewrite G3. rewrite rew_fbset2bool. reflexivity.
assert (X6: r'=fbset2bool r'_I). rewrite G4. rewrite rew_fbset2bool. reflexivity.
intros. rewrite X1 in H. rewrite  X2 in H. rewrite  X3 in H.  rewrite X5 in H. rewrite  X6 in H.
rewrite X4 in H. rewrite  X3 in H. Apply stepg1_lhs_R  in H.
simpl fst in H. simpl snd in H. rewrite <- X2 in H. rewrite <- X3 in H.
rewrite <- X5 in H. rewrite G2 in H. rewrite rew_fbset2bool in H.
assert (d=fbset2bool dO_I). rewrite G2 . rewrite rew_fbset2bool . reflexivity.
symmetry in G2. rewrite <- H0. rewrite <- X5. apply H. 
Qed.

