(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation
#</h1>#
-   Exporting the main lemmas of control block 

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import  dtrTransform.

(*Control Block properties during odd clock cycles w/o errors*)
Require Export controlStep0.
(*
step0_tcbv_C
step0_tcbv
*)
(*Control Block properties during even clock cycles w/o errors*)
Require Export controlStep1.
(*
step1_tcbv_C
step1_tcbv
stepr1_tcbv
*)
(*Control Block properties during odd clock cycles with errors*)
Require Export controlStepg0.
(*
stepg0_tcbv
step0_tcbv_i
*)
(*Control Block properties during even clock cycles with errors*)
Require Export controlStepg1.
(*
stepg1_tcbv
step1_tcbv_i
stepr1_tcbv_i
*)
(*Control Block properties during the DTR recovery process*)
Require Export controlRec.
(*
stepr2_tcbv_C
stepr2_tcbv
stepr3_tcbv
stepr4_tcbv
stepr5_tcbv
*)
