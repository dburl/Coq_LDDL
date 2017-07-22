(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-   file gathering all needed lemmas from that folder

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)
(*
Add LoadPath "..\".
Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\". *)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import dtrTransform relationPred.

Require Export relationProp.

(*
transf_dtr0
dtr1_r_imp_d'r 
dtr1_r_imp_rr'
dtrs1_imp_dtr1_d
dtrs1_imp_dtr1_d'
dtrs1_imp_dtr1_r
dtrs1_imp_dtr1_r'
dtrs0_imp_dtr0_d'
dtrs0_imp_dtr0_d
dtrs0_imp_dtr0_r
dtrs0_imp_dtr0_r'
dtrs0_imp_dtr0_dr
dtrs1_imp_dtr1_d'r
dtr1_d'_imp_d'r
dtr0_d_imp_dr
*)
Require Export memoryStep.
(*
step_dtrs0
step1_mb
	*)
Require Export memoryStepg0.
(*
step_dtrs0_fail
step0_mb_s
step0_mb_b
step0_mb_i
step0_mb_dr_F
step0_mb_rr'
step0_mb_d'
step0_mb_r
step0_mb_r'
stepg0_mb
	step0_mb_id' (local)
	step0_mb_if(local)
	step0_mb_dr(local)
*)
Require Export memoryStepg1.
(*
	step1_mb_f
	step1_mb_s
	step1_mb_b
	step1_mb_i 
	step1_mb_id'
	step1_mb_d 
	step1_mb_dF
	step1_mb_r
	step1_mb_d'r
	step1_mb_rr'
 	step1_mb_r'
 	stepg1_mb
 	step1_mb_if (local)
	*)
Require Export memoryRec.
(*
	stepr4_mb_d'rr'
	stepr3_mb_d'rr'
	stepr5_mb_rr'
	stepr2_mb_d'rr'
	*)
