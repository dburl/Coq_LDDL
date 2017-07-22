(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-   Properties of memory block sub-part called rhsPar

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

(* ##################################################################### *)
(** Properties of sub-circuit of Memory Block called rhsPar w/o Glitches *)
(* ##################################################################### *)

(* State before/after for both cycles w/o errors *)
Lemma step_rhs: forall si_I sav_I rol_I fai_I rO_I sav2_I t rhs2,
                step rhsPar {si_I,{{{ sav_I, rol_I},fai_I},{rO_I,sav2_I}}} t rhs2
             -> let rNew:= if ((beq_buset_t sav2_I (~?))&&(beq_buset_t si_I (~0))&&(beq_buset_t rO_I (~0))) then (~0)
                           else if (beq_buset_t sav2_I (~?))  then (~?)
                           else if (beq_buset_t sav2_I (~1)) then si_I
                           else rO_I in
                t= {{ {{sav_I,rol_I}, fai_I}, si_I}, rNew} /\ rhs2 = rhsPar.
Proof.
introv H. 
assert ( F:  fstep rhsPar {si_I, {sav_I, rol_I, fai_I, {rO_I, sav2_I}}}  = 
             Some ({{ {{sav_I,rol_I}, fai_I}, si_I}, 
                      if ((beq_buset_t sav2_I (~?))&&(beq_buset_t si_I (~0))
                      &&(beq_buset_t rO_I (~0))) then (~0)
                      else if (beq_buset_t sav2_I (~?))  then (~?)
                      else if (beq_buset_t sav2_I (~1)) then si_I
                      else rO_I},rhsPar)) by
(Destruct_s sav2_I; destruct x; cbn; Destruct_s sav_I;  Destruct_s rol_I; 
Destruct_s fai_I; Destruct_s si_I; Destruct_s rO_I; 
destruct x; destruct x0; destruct x1 ; destruct x2; destruct x3;
vm_compute; try easy). 
eapply fstep_imp_detstep in F; Simpl.
Qed.