
(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-  Definition of the relations between states of the source and transformed circuits.  
-  Relations between global transformed circuit (plugged with CB, IO buffers) and
     its source version (according to cycles, corruption, ...)

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".

Require Export dtrTransform.

Set Implicit Arguments.

(** Type of predicates on DTR memory block *)
(*three original memory cells (bits)  and their relations towards to the state of the transformed circuit*)
Definition Pmb0_type := bool -> bool -> bool-> bool -> bool -> bool -> Prop.
Definition Pmb1_type := bool -> bool -> bool-> bool -> bool -> bool -> bool -> Prop.

(* Definition of the different states of circuits upon normal execution  *)
(* There are 2 different states corresponding to execution cycles        *)
(*  2i-1 and 2i .                                                        *)
(* characterize the states of memory blocks at these steps               *)
(* dtrs c c' c'' c2 relates the state of the transformed circuit c2          *)
(* according to the states of the original circuit before (c)            *)
(* ,after  a reduction step(c'), and after two reduction steps (c'').     *)

(** ** Specification of possible corrupted states                  *)
(* Corruption of memory blocks at two different cycles *)

Section Def_dtrg.
Variable cmb0 : Pmb0_type.
Variable cmb1 : Pmb1_type.

Inductive dtr0: forall S T, circuit S T -> circuit S T -> circuit (S#((§ # §) # §)) (T#((§ # §) # §))-> Prop :=
| TgGate : forall S T (g:gate S T), 
            dtr0 (Cgate g) (Cgate g) (-|Cgate g, ID|-)
| TgPlug : forall S T (p:plug S T), 
           dtr0 (Cplug p) (Cplug p) (-|Cplug p, ID|-)
| TgSeq  : forall S T U (c1 c1':circuit S T) (c2 c2':circuit T U) c21 c22, 
           dtr0 c1 c1' c21 -> dtr0 c2 c2' c22 -> dtr0 (c1-o-c2) (c1'-o-c2') (c21-o-c22) 
| TgPar  : forall S T U V (c1 c1':circuit S T) (c2 c2':circuit U V) c21 c22, 
           dtr0 c1 c1' c21 -> dtr0 c2 c2' c22 
        -> dtr0 (-|c1,c2|-) (-|c1',c2'|-) ((SWAP_LR S U ctrBUS)-o--|c21,ID|--o-(SWAP_LS T ctrBUS U)-o--|ID, c22|--o-RSH )                                    
| TgLoop : forall S T (c c':circuit (S#§) (T#§)) c2 b b' d d' r r',
           dtr0 c c' c2 -> cmb0 b b' d d' r r'
        -> dtr0 (-{b}-c) (-{b'}-c') (memBlock d d' r r' c2).

Inductive dtr1: forall S T, circuit S T -> circuit S T -> circuit S T -> circuit (S#((§ # §) # §)) (T#((§ # §) # §))-> Prop :=
| Tg1Gate : forall S T (g:gate S T), 
            dtr1 (Cgate g) (Cgate g) (Cgate g) (-|Cgate g, ID|-)
| Tg1Plug : forall S T (p:plug S T), 
           dtr1 (Cplug p) (Cplug p) (Cplug p) (-|Cplug p, ID|-)
| Tg1Seq  : forall S T U (c1 c1' c1'':circuit S T) (c2 c2' c2'':circuit T U) c21 c22, 
           dtr1 c1 c1' c1'' c21 -> dtr1 c2 c2' c2'' c22 -> dtr1 (c1-o-c2) (c1'-o-c2') (c1''-o-c2'') (c21-o-c22) 
| Tg1Par  : forall S T U V (c1 c1' c1'':circuit S T) (c2 c2' c2'':circuit U V) c21 c22, 
           dtr1 c1 c1' c1'' c21 -> dtr1 c2 c2' c2'' c22 
        -> dtr1 (-|c1,c2|-) (-|c1',c2'|-) (-|c1'',c2''|-) ((SWAP_LR S U ctrBUS)-o--|c21,ID|--o-(SWAP_LS T ctrBUS U)-o--|ID, c22|--o-RSH )                                
| Tg1Loop : forall S T (c c' c'':circuit (S#§) (T#§)) c2 b b' b'' d d' r r',
           dtr1 c c' c'' c2 -> cmb1 b b' b'' d d' r r'
        -> dtr1 (-{b}-c) (-{b'}-c') (-{b''}-c'') (memBlock d d' r r' c2).
End Def_dtrg.
Hint Constructors dtr0.
Hint Constructors dtr1.

(*  Comparison cycle                                      *)
(*  Cases of correct cells in memory blocks   *)
Inductive cmb0: Pmb0_type:=
| Icmb0  : forall b b', cmb0 b b'  b' b' b' b.

(*  Different cases of corrupted cells in memory blocks   *)
(* Potential corruptions  *)

Inductive cmb0_d :Pmb0_type := 
| Icmb0d  : forall b b' z,   cmb0_d  b b'  z b' b' b.

Inductive cmb0_d' :Pmb0_type := 
| Icmb0d' : forall b b' z,   cmb0_d' b b'  b' z b' b.

Inductive cmb0_r :Pmb0_type := 
| Icmb0r  : forall b b' z,   cmb0_r  b b'  b' b' z b.

Inductive cmb0_r' :Pmb0_type := 
| Icmb0r' : forall b b' z,   cmb0_r' b b'  b' b' b' z.

Inductive cmb0_dr :Pmb0_type := 
| Icmb0dr : forall b b' y z, cmb0_dr b b'  y  b' z b.

Inductive cmb0_rr' :Pmb0_type := 
| Icmb0rr': forall b b' y z, cmb0_rr' b b' b' b' y z.

(* Actual corruptions ie will trigger an error *)
Inductive cmb0_D :Pmb0_type := 
| Icmb0D : forall b b',    cmb0_D b b'   (negb b')  b'    b' b.

Inductive cmb0_D' :Pmb0_type := 
| Icmb0D' : forall b b',   cmb0_D' b b'     b'  (negb b') b' b.

Inductive cmb0_Dr :Pmb0_type := 
| Icmb0Dr : forall b b' z, cmb0_Dr b b' (negb b')  b'     z  b.


Definition dtrs0   := dtr0 cmb0.
Definition dtr0_d  := dtr0 cmb0_d.
Definition dtr0_d' := dtr0 cmb0_d'.
Definition dtr0_r  := dtr0 cmb0_r.
Definition dtr0_r' := dtr0 cmb0_r'.
Definition dtr0_dr := dtr0 cmb0_dr.
Definition dtr0_rr':= dtr0 cmb0_rr'.


(*  Non comparison cycle                                  *)
(*  Cases of correct cells in memory blocks   *)
Inductive cmb1: Pmb1_type:=
| Icmb1  : forall b b' b'', cmb1  b b' b''   b'' b' b' b.


(*  Different cases of corrupted cells in memory blocks   *)
Inductive cmb1_d :Pmb1_type := 
| Icmb1d   : forall b b' b'' z,   cmb1_d   b b' b''   z   b' b' b.

Inductive cmb1_d' :Pmb1_type := 
| Icmb1d'  : forall b b' b'' z,   cmb1_d' b b' b''    b'' z  b' b.

Inductive cmb1_r :Pmb1_type := 
| Icmb1r   : forall b b' b'' z,   cmb1_r b b' b''     b'' b' z  b.

Inductive cmb1_r' :Pmb1_type := 
| Icmb1r'  : forall b b' b'' z,   cmb1_r' b b' b''    b'' b' b' z.

Inductive cmb1_d'r :Pmb1_type := 
| Icmb1d'r : forall b b' b'' y z,  cmb1_d'r b b' b''  b'' y  z  b.

Inductive cmb1_rr' :Pmb1_type := 
| Icmb1rr' : forall b b' b'' y z,  cmb1_rr' b b' b''  b'' b' y  z.


Definition dtrs1   := dtr1 cmb1.
Definition dtr1_d := dtr1 cmb1_d.
Definition dtr1_d':= dtr1 cmb1_d'.
Definition dtr1_r := dtr1 cmb1_r.
Definition dtr1_r':= dtr1 cmb1_r'.
Definition dtr1_d'r:= dtr1 cmb1_d'r.
Definition dtr1_rr':= dtr1 cmb1_rr'.


(* States during recovery *)

Inductive rec_rr' :Pmb0_type := 
| Irecrr' : forall b b' y z, rec_rr' b b' b' b y z.

Inductive rec_d'rr' :Pmb0_type := 
| Irecd'rr' : forall b b' x y z, rec_d'rr' b b' b' x y z.

Definition dtrec_rr'  := dtr0 rec_rr'.

Definition dtrec_d'rr'  := dtr0 rec_d'rr'.


(* ---------------------------------------------------------- *)
(** Relations between global transformed circuit and
    its source version (according to cycles, corruption, ...) *)
(* ---------------------------------------------------------- *)


(* The triplicated control block  in its different states *)
Definition cbs0 := ctrBlockTMR false false false.
Definition cbs1 := ctrBlockTMR false false true.
Definition cbs2 := ctrBlockTMR false true  false.
Definition cbs3 := ctrBlockTMR false true  true.
Definition cbs4 := ctrBlockTMR true  false false.
Definition cbs5 := ctrBlockTMR true  false true.

(*     States of the input buffer bank        *)
Definition ibs0 S (i:{|S|}) := dtrIB_T i i.
Definition ibs1 S (i i':{|S|}) := dtrIB_T i i'.

(*     States of the output buffer bank       *)
Definition obs0 T (a b:{|T|}) := dtrOB_T  a a a a b.
Definition obs1 T (a b:{|T|}) := dtrOB_T  a b a b b.

(* state of the 3 fail cells   *)
Definition nofail  := (false,false,false).
Definition sigfail := (true, true, true).


Inductive Dtrseven: forall S T, (circuit S T -> circuit S T -> circuit (S # ((§ # §) # §)) (T # ((§ # §) # §))-> Prop)
                             -> (circuit ((§ # §) # §) ((((§ # §) # §) # §) # §))
                             -> (circuit (S # §) S)
                             -> (circuit (T # (((§ # §) # §) # §)) ((T # (T # T)) # §))
                             -> circuit S T -> circuit S T -> (circuit S (T # (T # T))) -> Prop :=
| CDtrseven : forall S T (dtrs:circuit S T -> circuit S T -> circuit (S # ((§ # §) # §)) (T # ((§ # §) # §))-> Prop)
                          f cbs ibs obs 
                         (c c':circuit S T) (cc: circuit (S # ((§ # §) # §)) (T # ((§ # §) # §))), 
              dtrs c c' cc 
           -> Dtrseven dtrs cbs ibs obs c c' (globcir (f,f,f) cbs ibs cc obs).
Hint Constructors Dtrseven.


Inductive Dtrsodd: forall S T, (circuit S T -> circuit S T -> circuit S T -> circuit (S # ((§ # §) # §)) (T # ((§ # §) # §))-> Prop)
                             -> (bool*bool*bool)
                             -> (circuit ((§ # §) # §) ((((§ # §) # §) # §) # §))
                             -> (circuit (S # §) S)
                             -> (circuit (T # (((§ # §) # §) # §)) ((T # (T # T)) # §))
                             ->  circuit S T -> circuit S T -> circuit S T -> (circuit S (T # (T # T))) -> Prop :=
| CDtrsodd : forall S T (dtrs:circuit S T -> circuit S T -> circuit S T -> circuit (S # ((§ # §) # §)) (T # ((§ # §) # §))-> Prop)
                        (fs:bool*bool*bool) cbs ibs obs 
                        (c c' c'': circuit S T) (cc: circuit (S#((§ # §) # §)) (T#((§ # §) # §))), 
            dtrs c c' c'' cc 
         -> Dtrsodd dtrs fs cbs ibs obs c c' c'' (globcir (fst (fst fs),snd (fst fs), snd fs) cbs ibs cc obs).
Hint Constructors Dtrsodd. 


Definition Dtrs0 S T     := Dtrseven (@dtrs0 S T) cbs0.
Definition Dtr0_d S T   := Dtrseven (@dtr0_d S T) cbs0. 
Definition Dtr0_d' S T  := Dtrseven (@dtr0_d' S T) cbs0. 
Definition Dtr0_r S T   := Dtrseven (@dtr0_r S T) cbs0. 
Definition Dtr0_r' S T  := Dtrseven (@dtr0_r' S T) cbs0.
Definition Dtr0_rr' S T := Dtrseven (@dtr0_rr' S T) cbs0.
Definition Dtr0_dr S T  := Dtrseven (@dtr0_dr S T) cbs0. 

(* Definition Dtr0_Dr S T  := Dtrseven (@dtr0_dr S T) cbs0. *)

(* possible states during recovery *)
Definition Dtr2_d'rr' S T  := Dtrseven (@dtrec_d'rr' S T) cbs2.
Definition Dtr3_d'rr' S T  := Dtrseven (@dtrec_d'rr' S T) cbs3.
Definition Dtr4_d'rr' S T  := Dtrseven (@dtrec_d'rr' S T) cbs4.
Definition Dtr5_d'rr' S T  := Dtrseven (@dtrec_d'rr' S T) cbs5.


Definition Dtr2_rr' S T  := Dtrseven (@dtrec_rr' S T) cbs2.
Definition Dtr3_rr' S T  := Dtrseven (@dtrec_rr' S T) cbs3.
Definition Dtr4_rr' S T  := Dtrseven (@dtrec_rr' S T) cbs4.
Definition Dtr5_rr' S T  := Dtrseven (@dtrec_rr' S T) cbs5.


(* possible states during recovery *)
Definition Dtr2_d' S T  := Dtrseven (@dtr0_d' S T) cbs2.
Definition Dtr3_d' S T  := Dtrseven (@dtr0_d' S T) cbs3.
Definition Dtr4_d' S T  := Dtrseven (@dtr0_d' S T) cbs4.
Definition Dtr5_d' S T  := Dtrseven (@dtr0_d' S T) cbs5.


Definition Dtrs1 S T    := Dtrsodd (@dtrs1 S T)    nofail cbs1.
Definition Dtr1_d S T   := Dtrsodd (@dtr1_d S T)   nofail cbs1.
Definition Dtr1_r S T   := Dtrsodd (@dtr1_r S T)   nofail cbs1.
Definition Dtr1_r' S T  := Dtrsodd (@dtr1_r' S T)  nofail cbs1.
Definition Dtr1_d'r S T := Dtrsodd (@dtr1_d'r S T) nofail cbs1. 
Definition Dtr1_rr' S T := Dtrsodd (@dtr1_rr' S T) nofail cbs1.

(* d' and r are corrupted and fail signal has been raised *)
Definition Dtr1_d'rf S T := Dtrsodd (@dtr1_d'r S T) sigfail cbs1. 

(* d is corrupted and fail signal has been raised *)
Definition Dtr1_df S T := Dtrsodd (@dtr1_d S T) sigfail cbs1. 