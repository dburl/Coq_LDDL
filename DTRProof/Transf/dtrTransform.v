(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
-   Definition of DTR subcircuits (IB buffers, control block, memory block)

-   definition of the syntactic transformation

          Dmitry Burlyaev - Pascal Fradet - 2015
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".

Require Export tmrMainTh CirReflect.

Set Implicit Arguments.

(* ------------------  Small Common Circuits Definitions  ------------------*)

(* Control bus for mem Block- collection of 3 control wires (save,rollBack,fail)*)
Definition ctrBUS:=((§ # §) #§). 

(* Build a bus of type S with values (bool2bset b)   *)
(* ex.: buildBus ((§#§)#§) false = {{~0,~0},~0}      *)
(* Used in initialization :                          *)
(*  dtrInpT S (buildBus S false) (buildBus S false)  *)

Fixpoint buildBus S (b:bool) : {|S|} := 
match S with 
| Wire       => bool2bset b
| Pbus S1 S2 => {buildBus S1 b,buildBus S2 b}
end.

Lemma pure_buildBus : forall S b, pure_bset (buildBus S b).
Proof.
intros. induction S; cbn.
- CheckPure.
- eauto.
Qed. 

(* ------------------  Control Block sub-circuits Definitions  ------------------*)

(* There are 4 mem cells : fail, A, B,C.
A,B,C are used for FSM encoding; fail mem- just a delay.
Below we define the next state of A, B, or C from their prev.values*)

(*(A#(B#C)) -> nxt A*)
Definition nxtA:circuit (§ # (§ # §)) § :=
           FORK -o- -| -|NOT,ID-o-AND|- -o-AND,-|ID,-|NOT,NOT|--o-AND|--o-AND |--o-OR.

(*((A#(B#C))#fail) -> nxt b*)
Definition nxtB:circuit ((§ # (§ # §))#§) § :=
(*-|-|ID,-|ID,ID|-|--o- *)
           -|FORK -o--|-|NOT,-|NOT,ID|--o-AND|--o-AND,-|NOT,-|ID,NOT|--o-AND|--o-AND|-,ID|- (*fail in parall*)
                  -o- (SWAP_LR § § §) -o--|AND,ID|--o-OR.

(*((A#(B#C))#fail) -> nxt c*)
Definition nxtC:circuit ((§ # (§ # §))) § :=
(*-|ID,-|ID,ID|-|--o- *)
           FORK-o--|ID,FORK|- (*(A #(B # C))#((A #(B # C))#(A #(B # C)))*)
               -o--| -|NOT,-|NOT,NOT|--o-AND|--o-AND,-| -|NOT,-|ID,NOT|--o-AND|--o-AND,
                     -|ID,-|NOT,NOT|--o-AND|--o-AND|--o-OR|--o-OR.

(*The whole combin circuit of non-TMRed control block*)
(*(fail#(A#(B#C))) -> nxt (A#(B#C))*)
Definition ctrCombin: circuit (§#(§ # (§ # §))) (§ # (§ # §)) :=
           SWAP-o--| (*-|ID,-|ID,ID|-|--o-*) FORK-o--|nxtA,FORK|-,ID|-
               -o-(SWAP_LS § ((§ # (§ # §)) # (§ # (§ # §))) (§ ))  (*A # ((fail) # ((A # (B # C)) # (A # (B # C))))*)
               -o--|ID, (SWAP32 § (§ # (§ # §)) (§ # (§ # §))) -o--|nxtC,nxtB|--o-SWAP|-.

(*Signals regrouping and final circuit definition with memory cells*)

(*signals re-grouping*)
Definition ctrBusGr: circuit (((§ # §) # §) # §) (§ # (§ # (§ # §))) := 
            -|LSH,ID|--o-LSH-o--|ID,LSH|-.
Definition ctrBusGr3: circuit  (((§#(§ # §)  ) ) # (§ # (§ # §))) (((((§#(§ # §) ) ) # §) # §) # §):= 
           -|ID,RSH|--o-RSH-o--|RSH,ID|-.
Definition ctrBusGr4: circuit (((§ # §) # §) # §) ((§ # (§ # §)) # (§ # (§ # (§ # §)))) :=
           ctrBusGr-o-(DUPL § (§ # (§ # §)) )-o-SWAP.

(*[Def]:: single copy of ctrBlock FSM*)
(*[Type]:failM_out-> failMem#(A#(B#C))*)
Definition ctrFSM_dtr (A B C: bool): circuit § (§#(§#(§ # §))) :=
           FORK-o--|ID,-{A}-(-{B}-(-{C}-(-|-|-|ID,ID|-,ID|-,ID|-
               -o-ctrBusGr4-o--|ID,ctrCombin|--o-ctrBusGr3)))|-. (* (failMem # (A # (B # C)))*)


(*Output circuit definition- combin.circuits after FSM*)
(*save: A(B C)-> save*)
Definition save_dtr: circuit ( § # (§ # §))  § :=
           FORK-o- -| -|NOT,-|NOT,ID|--o-AND|--o-AND,-|ID,-|NOT,ID|--o-AND|--o-AND |--o-OR.

(*rollBack:: fail(A(B C))-> rollBack*)
Definition rollBack_dtr: circuit  (§ #( § # (§ # §)))  §:=
           (* -|ID,-|ID,-|ID,ID|-|-|--o--|ID,FORK-o-FORK-o-*)
           -|ID,FORK-o-FORK-o--|-|-|NOT,-|NOT,ID|--o-AND|--o-AND,-|NOT,-|ID,NOT|--o-AND|--o-AND|-
          ,-|-|NOT,ID-o-AND|--o-AND,-|ID,-|NOT,NOT|--o-AND|--o-AND|--o-OR |-|- 
           -o--|ID,LSH-o--|ID,OR|-|--o-RSH-o--|AND,ID|--o-OR.

(*rB: fail(A(B C))-> rB*)
Definition rB_dtr: circuit (§ #( § # (§ # §)))   §:=
(* -|ID,-|ID,-|ID,ID|-|-|--o-*)
           -|ID,FORK-o--|-|NOT,-|NOT,ID|--o-AND|--o-AND,-|NOT,-|ID,NOT|--o-AND|--o-AND|-|-
            -o-RSH-o--|AND,ID|--o-OR.

(*subst: fail(A(B C))-> subst*)
Definition subst_dtr: circuit (§ #( § # (§ # §)))  §:=
(*-|ID,-|ID,-|ID,ID|-|-|--o-*)
          -|ID,  FORK-o--| -|NOT,-|NOT,ID|--o-AND|--o-AND,
            FORK-o--|-|NOT,-|ID,NOT|--o-AND|--o-AND,-|NOT,ID-o-AND|--o-AND|- -o-OR|-|-
           -o-RSH-o--|AND,ID|--o-OR.

(*[Def]:: single copy of control Block with proper outputs*)
(*[Type]:: failM_out-> (save#rollBack)#(rB#subst)*)
Definition ctrBl_dtr ( A B C: bool) : circuit § ((((§ # §)#§)#§) #§)  :=
          (ctrFSM_dtr A B C)-o-FORK-o--|-|ID,FORK|--o-(SWAP_RL § (§ #(§ # §)) (§ #(§ # §)))
          -o--|save_dtr,rollBack_dtr|-,FORK-o--|rB_dtr,subst_dtr|-|-
          -o--|ID,-|FORK,ID|- |--o-RSH-o--|RSH,ID|-.

(*[Def]:: 5 voters located after triplicated control block. they return 5 ctr sygnals*)
Definition ctrVoting : circuit ((((((§ # §) # §) # §) # §) # ((((§ # §) # §) # §) # §)) # ((((§ # §) # §) # §) # §)) 
                               ((((§ # §) # §) # §) # §) := 
           -|shuffle (((§ # §)#§)#§) § (((§ # §)#§)#§)  § ,ID|--o--|-|shuffle ((§ # §)#§) § ((§ # §)#§)  §, ID|- ,ID|-
          -o--|-|-|shuffle (§ # §) § (§ # §)  §,ID|-, ID|- ,ID|--o--|-|-|-|shuffle § § § §, ID|-,ID|-, ID|- ,ID|- 
          -o-(shuffle  ((((§ # §) #(§ # §)) # (§ # §))#(§ # §)) (§ # §) (((§ # §)#§)#§) §)
          -o--|(shuffle  (((§ # §) #(§ # §)) # (§ # §)) (§ # §) ((§ # §)#§) §),ID|-
          -o--|-|(shuffle  ((§ # §) #(§ # §))  (§ # §) (§ # §) §),ID|-,ID|-
          -o--|-|-|(shuffle  (§ # §) (§ # §) §  §),ID|- ,ID|-,ID|-
          -o--|-|-|-|Voter31, Voter31|-,Voter31|-, Voter31|-,Voter31|-. (* ((((save # rollBack) # fail) # rB) # subst)) *)

(*[Def]:: TMR CONTROL BLOCK- FINAL*)
(*[Type]: ((failM1#failM2)#failM3) ->  ((((save # rollBack) # fail) # rB) # subst))  *)
Definition ctrBlockTMR ( A B C: bool) : circuit ((§#§)#§)  ((((§ # §) # §) # §) # §)  :=
          (tmr (ctrBl_dtr A B C))-o-ctrVoting.


(* ------------------  Memory Block sub-circuits Definitions  ------------------*)

(*[Def]:: rhs of memory block- it's is separated for simplisity*)
(*lhs of memory block with r-d cells are organised thrhough loop-structure and provide inputs to this
rhs part*)
Definition memBlRight (r' d':bool): circuit ((§ #§) #(§#§)) (§ # §) :=
(*-|-|ID, ID|-,-|ID, ID|-|- (*(r,d)#[save#rollBack]*)
-o-*)
          -|-|ID, FORK|-,-|FORK, ID|-|- (*(r,{d,d})#[{s,s}#rollBack]*)
          -o-(shuffle § (§ #§) (§ #§) §) (*(r,{s,s})#[{d,d}#rollBack]*)
          -o--|RSH-o--|CelbE r', ID|-,LSH|- (*(r',s)#[d,{d#rollBack}]*)
          -o-RSH -o--|LSH-o-(SWAP_RL § § §)-o--|ID,SWAP|--o-Mux21,ID|-(*  (mu # (d # rollBack)) *)
          -o--|ID, -|FORK-o--|(Celb d')-o-FORK,ID|-,ID|-|- (* (mu # (((d' # d') # d) # rB)) *)
          -o--|ID, -|LSH-o--|ID, eqG|- , ID|-|- (*   (mu # ((d' # fail) # rB))   *)
          -o--|ID, SWAP-o-RSH|- (*   (mu # ((rB # d') # fail))   *)
          -o-RSH -o--|SWAP-o-LSH,ID|- (*((rB # (d' # mu)) # fail)*)
          -o--|Mux21,ID|-.
(* all known parts and w/o unkinown S bus*)
(*   (((save # rollBack) # failI) # (d_O # r_O)) ->  ((so # ((save # rollBack) # failUpd)) # (r_O # save))*)
Definition lhsPar (r' d':bool) : circuit ((( § #  §) #  §) # ( § #  §)) ((§ # ((§ # §) # §)) # (§ # §)) := 
(*   (((save # rollBack) # failI) # (d_O # r_O)) *)
           RSH-o-LSH-o--|-|FORK,ID|-,SWAP|- (*((((save1.1 # rollBack) # (save1.2 # rollBack)) # fail) # (r_O # d_O))*)
           -o-LSH-o-(shuffle (§#§) (§#§) § (§#§) ) (*(( save1.1 # rollBack) # fail) # ((save1.2 # rollBack) # (r_O # d_O)))*)
           -o--|ID, SWAP -o- -|-|FORK, ID|--o-LSH,ID|--o-LSH-o--|ID,(memBlRight r' d')|-|- 
         (*(((save1.1 # rollBack) # fail) # (r_O # (so # failF)))*)
           -o--|-|-|FORK, ID|--o-LSH,ID|--o-LSH,ID|- (*((save1.1.1 # ((save1.1.2 # rollBack) # fail)) # (r_O # (so # failF)))*)
           -o-(shuffle § ((§ # §) # §) § (§ # §)) (*((save1.1.1 # r_O) # (((save1.1.2 # §) # §) # (so # failF)))*)
           -o--|SWAP,(shuffle (§ # §) § § §)-o--|ID,OR|--o-(SWAP_LR (§ # §) § §)-o-SWAP |- (*((r_O # save) # (((save # rollBack) # so) # failUpd))*)
         -o-SWAP-o-LSH-o-RSH.

Definition lhsMB (r' d':bool)  (S : bus): 
           circuit (((S # ((§ # §) # §)) # §)# §) (((S # §) # ((§ # §) # §)) # (§ # §)) :=
           LSH-o-LSH-o--|ID, (lhsPar r' d')|--o-RSH-o--|RSH,ID|-.

(* all known parts and w/o unkinown T bus*)
(*((si1 # ({save#rollBack} # failF)) # (r_O # save)) -> ( [((§ # §) # §) # s1 ]# rNew)*)
Definition rhsPar:circuit ( § # ((( § #  §) #  §) # ( § #  §))) ((((§ #§) # §) # §) # §) := 
           -|FORK,ID|- (*   (((si1#si2) # ((§ # §) # §)) # (r_O # save))   *)
          -o-LSH-o--|ID,RSH-o--|SWAP,SWAP|--o-LSH (*   si1 # [((§ # §) # §) # (si2 # (save # r_O))]   *)
          -o--|ID,(SWAP_RL  § § §)-o--|ID, SWAP|--o-Mux21|-|- (*    s1 #[((§ # §) # §) # rNew]  *)
          -o-RSH-o--|SWAP,ID|-.

(*(((T # si1) # ({save#rollBack} # failF)) # (r_O # save)) -> ( [(T # ((§ # §) # §)) # s1 ]# rNew)*)
Definition rhsMB   (T : bus) : circuit  (((T # (§)) # (( §# §) #  §)) # ( § #  §))
                                        (((T # ((§ # §) # §) ) # §) # §) :=
           LSH-o-LSH-o--|ID,(rhsPar)|- -o- RSH-o--|RSH,ID|-.

(*DTR memory block with parametrized internal sub-circuit, to be used to specify the corrupted state*)
Definition mbcore S T dN rN 
                           (lhsPar':circuit ((( § #  §) #  §) # ( § #  §)) ((§ # ((§ # §) # §)) # (§ # §)))
                           (c1':circuit  ((S#§)#((§#§)#§)) ((T#§)#((§#§)#§)) )
                           (rhsPar':circuit ( § # ((( § #  §) #  §) # ( § #  §))) ((((§ #§) # §) # §) # §) )
:= 
 (-{ dN}- (-{ rN}- ((LSH) -o- ((LSH) -o- ((-| ID, lhsPar' |-) -o- ((RSH) -o- (-| RSH, ID |-))))) -o-
 ((-| c1', ID |-) -o- ((LSH) -o-((LSH) -o- ((-| ID, rhsPar' |-) -o- ((RSH) -o- (-| RSH, ID |-)))))))).

(*[Def]:: MEMORY BLOCK- FINAL*)
Definition memBlock (d d' r r': bool) (S T: bus) (unknownCir: circuit ((S#§)#((§#§)#§)) ((T#§)#((§#§)#§))) :
                       circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)) :=
           -{d}-( -{r}-(  (lhsMB  r' d' S ) -o--|unknownCir,ID|--o-(rhsMB T)) ).

(* ------------------  Input Buffer sub-circuits Definitions  ------------------*)

(*[Type]: pi,rB-> ci: paper notation*)
Definition inpBufDTR (b b':bool):circuit (§ # §) § :=
           -|FORK-o--|ID, (Celb b) -o- (Celb b')|-,ID|--o-SWAP-o-Mux21.

(* ------------------  Output Buffer sub-circuits Definitions  ------------------*)
(*easier to define the circuit going from left to write according to the paper figure: paper notation*)
(*(co#save)->p'#(sub#oA)*)
Definition inbL1_dtr (p p' o:bool):circuit (§ # §) (§#(§ # §)) :=
           -|FORK-o--|(Celb p)-o-(Celb p'),ID|-,ID|- (* ((p' # co) # save)  *)
           -o-(SWAP_LS § § §)-o--|ID,-|ID,FORK-o--|(Celb o)-o-FORK,ID|-|-|- (* (p' # (save # ((oA # oA) # co))) *)
           -o--|ID,-|ID,(SWAP_LR § § §)|-|-  (* (p' # (save # ((oA # co ) # oA ))) *)
           -o--|ID,(SWAP32 § (§#§) §)-o--|ID,SWAP|-|- (* (p' # (oA # ( save # (oA # co))))   *)
           -o--|ID,-|ID, Mux21|--o-SWAP|-. (* (p' # (sub # oA)   *)

(*(co#save)  ->  ((o'' # o') # (sub# p')) # fail   *)
Definition inbL2_dtr (p p' o o' o'' :bool):circuit (§ # §) (((§ # §) # (§ # §)) # §) :=
          (inbL1_dtr p p' o)-o-(SWAP32 § § §)  (*(oA#(sub#p') *)
          -o--|FORK-o--|(Celb o')-o-FORK,ID|-,ID|-  (*(((o'# o') # o)#(sub#p') *)
          -o--|(SWAP_LS § § §)-o--|FORK,XOR|- ,ID|-   (*  (((o' # o') # fail) # (sub# p'))   *)
          -o--| -|-|Celb o'',ID|-,ID|- ,ID|-  (*((o'' # o') # fail) # (sub # p')*)
          -o-(SWAP_LR (§ # §) § (§ # §)). (* ((o'' # o') # (sub# p')) # fail *)

(*(rollBack#subst)-> muxA#(muxB#muxC)*)
Definition ob_topAnd : circuit (§ # §) ((§ # §)# §) :=
           -|FORK,FORK|--o-(shuffle § § § §)-o--|-|FORK,FORK|-,AND|--o--|(shuffle § § § §)-o--|AND,AND|-,ID|-. 

(*(co#save) -> ((p' # sub) # ((o'' # sub) # (o' # sub))) # fail *)
Definition inbL3_dtr (p p' o o' o'' :bool):circuit (§ # §) (((§ # §) # ((§ # §) # (§ # §))) # §) :=
           (inbL2_dtr p p' o o' o'') (* ((o'' # o') # (sub# p')) # fail *)
           -o--| -|ID,-|FORK-o--|FORK,ID|-,ID|-|-,ID|- (*((o'' # o') # (((sub # sub) # sub) # p')) # fail *)
           -o--| -|ID,SWAP_LS (§ # §) § § |- ,ID|-(*((o'' # o') # (((sub # sub) # ((p' # sub))) # fail *)
           -o--| SWAP32 (§ # §) (§ # §) (§ # §) ,ID|-(*((p' # sub) # ((sub # sub) # (o'' # o'))) # fail*)
           -o--| -|ID, (shuffle § § § §)-o--|SWAP,SWAP|- |- ,ID|-. (*((p' # sub) # ((o'' # sub) # (o' # sub))) # fail*)

(*output buffer- only with useful signal*)
(*((co#save)#(rollBack#subst))-> ((poA # (poB # poC)) # fail)*)
Definition outb_dtr (p p' o o' o'' :bool):circuit ((§ # §) # (§ # §)) ((§ # (§ # §)) # §) :=
           -|(inbL3_dtr p p' o o' o''), ob_topAnd-o-SWAP|-(*((p' # sub) # ((o'' # sub) # (o' # sub))) # fail*)
           -o-(SWAP_LR ((§ # §) # ((§ # §) # (§ # §))) § (  §#(§ # §))) (*(((p' # sub) # ((o'' # sub) # (o' # sub))) # (mux #(mux # mux) )) # fail*)
           -o--| shuffle (§ # §) ((§ # §)#(§ # §)) § (§ # §),ID|- (*(((p' # sub) # mux) # (((o'' # sub) # (o' # sub)) # (mux # mux))) # fail*)
           -o--| -|SWAP-o-Mux21,(shuffle (§ # §) (§ # §) §  §)-o--|SWAP-o-Mux21,SWAP-o-Mux21|--o-SWAP |-,ID|-. (*(poA # (poB # poC)) # fail*)

(*outbuffer where fail is also an input - and it is OR-ed with the local fail to provide update version to output*)
(*(((co#save)#(rollBack#subst)#fail))-> ((poA # (poB # poC)) # fail)*)
Definition outBuf_dtr (p p' o o' o'' :bool):circuit (((§ # §) # (§ # §)) # §) ((§ # (§ # §)) # §) :=
           -|outb_dtr p p' o o' o'',ID|--o-LSH-o--|ID,OR|-. 

(*[Def]:: OUTPUT BUFFER- FINAL*)
(*[Type]:co#(((save#rollBack)#fail)#subst)-> ((poA # (poB # poC)) # fail)*)
Definition outBufDTR (p p' o o' o'' :bool):circuit (§ # (((§ # §)#§) # §)) ((§ # (§ # §)) # §) :=
           -|ID,LSH -o--|ID,SWAP|- |-(*co#(((save#rollBack)#(subst #fail))*)
           -o-RSH-o--|RSH,ID|--o-LSH-o--|ID,RSH|--o-RSH-o-(outBuf_dtr p p' o o' o'').


(* Plugs used to add the output buffer bank to the circuit *)
Definition plug1_OB (S1 S2 S3 S4 S5 S6:bus) : circuit ((S1 # S2) # (((S3 # S4) # S5)#S6)) 
                                                    (((S2 # S1) # (((S3 # S4) # S5)#S6)) # ((S3 # S4)#S6)) := 
          -|SWAP,ID|--o--|ID,LSH-o--|ID,SWAP|--o-RSH-o--|FORK,ID|--o-LSH-o--|ID,SWAP|-
          -o-RSH-o--|LSH-o--|ID,SWAP|--o-RSH,ID|-|--o-RSH.

Definition plug2_OB (S1 S2 S3 S4 S5:bus) : circuit ((S1 # (S2 # S3)) # (S4 # S5))
                                                   (S2 # (S1 # ((S4 # S3) # S5))):= 
          -|SWAP-o-LSH-o--|ID,SWAP|-,ID|--o-LSH-o--|ID, LSH-o--|ID,RSH-o--|SWAP,ID|-|- |- .


Definition plug3_OB (S1 S2 S3 S4 S5 S6 S7:bus) : circuit ((S1 # (S2 # S3)) # ((S4 # (S5 # S6)) # S7))
                                                          (((S1 # S4) # ((S2 # S5) # (S3 # S6))) # S7) := 
          RSH-o--|LSH-o--|ID,SWAP|--o-RSH-o--|RSH,ID|-,ID|-
          -o--|LSH-o--|ID,RSH-o--|LSH-o--|ID,SWAP|--o-RSH,ID|--o-LSH|-,ID|- 
          -o--|-|ID,-|SWAP,SWAP|-|-,ID|-.

(* ####################################################### *)
(** *   The Double Time Redundancy (DTR) transformation    *)
(*                     FPGA'15 paper version               *)
(* ####################################################### *)

(* Building an input buffer bank of type S *)
Fixpoint dtrIB_T (S:bus) : {|S|} -> {|S|} -> circuit (S#§) S.
intros s1 s2.
destruct S. 
- exact (inpBufDTR (fbset2bool s1) (fbset2bool s2) ).
- Inverts s1. Inverts s2.
  exact  ( -|ID,FORK|--o-(shuffle S1 S2 § §)
                -o--|dtrIB_T S1 H1 H3, dtrIB_T S2 H2 H4|- ).
Defined.

(* Building an output buffer bank of type T *)
Fixpoint dtrOB_T (T:bus) : {|T|} -> {|T|} -> {|T|} -> {|T|} -> {|T|} -> circuit (T#(§ # § # § # §)) ((T#(T#T))#§).
intros p p' o o' o''.
destruct T. 
- exact (outBufDTR (fbset2bool p) (fbset2bool p') (fbset2bool o) (fbset2bool o') (fbset2bool o'')).
- Inverts p. Inverts p'. Inverts o. Inverts o'. Inverts o''.
  exact  ((plug1_OB T1 T2 §  § § §)
          -o--|LSH-o--|ID,(dtrOB_T  T1 H1 H3 H5 H7 H9)|-,ID|--o-(plug2_OB T2 (T1#(T1#T1)) § (§#§) §)
          -o--|ID,(dtrOB_T  T2 H2 H4 H6 H8 H10) |--o- (plug3_OB T1 T1 T1 T2 T2 T2 §)).
Defined.

(*[Def]:: transformation to replace all memory cells with memory blocks*)
(*[Type]: : forall S T : bus, circuit S T -> circuit (S # ctrBUS) (T # ctrBUS)*)

Fixpoint dtrMemT S T (c: circuit S T): circuit (S#(§#§#§)) (T#(§#§#§)) :=
         match c with
       | Cgate g             => -|Cgate g, ID|- 
       | Cplug p             => -|Cplug p, ID|-
       | Cseq c1 c2          => (dtrMemT c1) -o- (dtrMemT c2)
       | @Cpar s t u v c1 c2 => (SWAP_LR s u (§#§#§))-o--|dtrMemT c1,ID|-
                             -o-(SWAP_LS t (§#§#§) u)-o--|ID,dtrMemT c2|--o-RSH 
       | Cloop b c           => memBlock  b b b b (dtrMemT c)
end. 

(** Macros for the composition of the four components :   *)
(**  control block, input buffers, output buffers, and   *)
(** transformed circuit with memory blocks               *)

Definition dtrcore S T (c1:circuit (S # §) S)
                       (c2:circuit (§ # § # §) (§ # §# § # § # §))
                       (c3:circuit (S # (§ # § # §)) (T # (§ # § # §)))
                       (c4:circuit (T # (§ # § # § # §)) (T # (T # T) # §))
          := LSH-o-((LSH) -o- ((-| ID, RSH |-) -o- ((-| ID, c2|-) -o-
             ((RSH) -o-((-| RSH, ID |-) -o-((-|(LSH) -o-
             ((-| ID, SWAP |-) -o-((RSH) -o- ((-|c1, ID |-) -o- (c3)))),ID |-) -o-
             (((LSH) -o- c4) -o-((-| ID, (FORK) -o- (-| FORK, ID |-) |-) -o-
             ((RSH) -o- (-| RSH, ID |-)))))))))). 

Definition globcir S T (f3 : bool*bool*bool) 
                       (cbs: circuit ((§ # §) # §) ((((§ # §) # §) # §) # §))
                       (ibs: circuit (S # §) S)
                       (cc :  circuit (S # ((§ # §) # §)) (T # ((§ # §) # §))) 
                       (obs: circuit (T # (((§ # §) # §) # §)) ((T # (T # T)) # §)) := 
                       let (ff,f''):=f3 in let (f,f') := ff in
                      -{f}-(-{f'}-(-{f''}-dtrcore ibs cbs cc obs)).

(*[Def]:: Main transformation. It combine the control block (and a triplicated cell 
          to record the fail signal value) with input and output buffers
          (whose cells are initialized to false) and the transformed circuit with
          memory blocks (whose 4-cells are initialized with the value of the original circuit) *)

Definition DTR S T (c: circuit S T) : circuit S (T#(T#T)) := 
           globcir (false,false,false) 
                   (ctrBlockTMR false false false)
                   (dtrIB_T (buildBus S false) (buildBus S false))
                   (dtrMemT c)
                   (dtrOB_T (buildBus T false)(buildBus T false) (buildBus T false) 
			    (buildBus T false)(buildBus T false)).
