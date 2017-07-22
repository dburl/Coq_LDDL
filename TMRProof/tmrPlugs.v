(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The triple modular redundancy transformation   
#</h1>#    
- Basic properties about plugs

              Pascal Fradet - Inria - 2014  
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\Common\".
Require Export tmrDef.

Set Implicit Arguments.


Lemma emG_corrupts : forall S (a:{|S|}) b, pure_bset a -> atmost1glitch b 
                                -> eq_mod_G {a,a,a} b -> corrupt_1in3_bus a b.
Proof.
introv H1 H2 H.
Destruct_s b as b1 b2. Destruct_s b1.
Inverts H2; Inverts H5; Inverts H; Inverts H5.
- apply emG_pure in H11; try easy; subst.
  apply emG_pure in H12; try easy; subst.
  easy.
- apply emG_pure in H11; try easy; subst.
  apply emG_pure in H3; try easy; subst.
  easy.
- apply emG_pure in H3; try easy; subst.
  apply emG_pure in H12; try easy; subst.
  easy.
Qed.


Lemma cle11_tmr : forall S T c, @corrupt_1in3_cir1 S T c (tmr c).
Proof. introv. induction c; constructor; fold tmr; easy. Qed.

Lemma cle12_tmr : forall S T c, @corrupt_1in3_cir2 S T c (tmr c).
Proof. introv. induction c; constructor; fold tmr; easy. Qed.

Lemma cle13_tmr : forall S T c, @corrupt_1in3_cir3 S T c (tmr c).
Proof. introv. induction c; constructor; fold tmr; easy. Qed.


(** *     Properties about plugs used in the tmr transformation  *)

(** **    Properties about standard reduction                    *)

Lemma fact_votmr : forall S a1 a2 a3 b, 
                   step (votmr S) {a1,a2,a3,b,b,b} {{a1,b},{a2,b},{a3,b}} (votmr S).
Proof. 
intros. apply redcomb_imp_step.
- repeat constructor.
- Destruct_s b as b. destruct b; easy.
Qed.


Lemma fact_shuf1 : forall S T a1 a2 a3 b1 b2 b3, 
                   step (shuf1 S T) {{a1,b1},{a2,b2},{a3,b3}} {{a1,a2,a3},{b1,b2,b3}} (shuf1 S T).
Proof.
intros. Apply redcomb_imp_step.
Qed.

Lemma fact_shuf2 : forall S T a1 a2 a3 b1 b2 b3, 
                   step (shuf2 S T) {{a1,a2,a3},{b1,b2,b3}} {{a1,b1},{a2,b2},{a3,b3}}  (shuf2 S T).
Proof.
intros. Apply redcomb_imp_step.
Qed.


Lemma fact_shuf3 : forall S a1 a2 a3 b1 b2 b3, 
                   step (shuf3 S) {{a1,b1},{a2,b2},{a3,b3}} {a1,a2,a3,b1,b2,b3} (shuf3 S).
Proof.
intros. Apply redcomb_imp_step.
Qed.


(** **    Properties about standard reduction on corrupted signals   *)

(** *** About shuf1    *)

Lemma shuf1_corrupt1: forall S T a b c sss aaa bbb,
                       corrupt_1in3_bus1 {a,b} sss 
                    -> step (shuf1 S T) sss {aaa,bbb} c
                    -> corrupt_1in3_bus1 a aaa /\ corrupt_1in3_bus1 b bbb.
Proof.
introv C H. Dd_buset_all.
assert (X:step (shuf1 S T) {x9, x11, {x, x10}, {x7, x8}} {x9, x, x7, {x11, x10, x8}} (shuf1 S T))
    by (apply fact_shuf1). 
Detstepres H X. Inverts C; SimpS; easy. 
Qed.

Lemma  shuf1_corrupt2: forall S T a b c sss aaa bbb,
                       corrupt_1in3_bus2 {a,b} sss 
                    -> step (shuf1 S T) sss {aaa,bbb} c
                    -> corrupt_1in3_bus2 a aaa /\ corrupt_1in3_bus2 b bbb.
Proof.
introv C H. Dd_buset_all.  
assert (X:step (shuf1 S T) {x9, x11, {x, x10}, {x7, x8}} {x9, x, x7, {x11, x10, x8}} (shuf1 S T))
    by (apply fact_shuf1). 
Detstepres H X. Inverts C; SimpS; easy.
Qed.

Lemma  shuf1_corrupt3: forall S T a b c sss aaa bbb,
                       corrupt_1in3_bus3 {a,b} sss 
                    -> step (shuf1 S T) sss {aaa,bbb} c
                    -> corrupt_1in3_bus3 a aaa /\ corrupt_1in3_bus3 b bbb.
Proof.
introv C H. Dd_buset_all.  
assert (X:step (shuf1 S T) {x9, x11, {x, x10}, {x7, x8}} {x9, x, x7, {x11, x10, x8}} (shuf1 S T))
    by (apply fact_shuf1). 
Detstepres H X. Inverts C; SimpS; easy.
Qed.

Lemma stepg_shuf1 : forall S T a b c aaa bbb, 
                    pure_bset {a,b}
                 -> stepg (shuf1 S T) {{a,b},{a,b},{a,b}} {aaa,bbb} c
                 -> (corrupt_1in3_bus a aaa /\ bbb={b,b,b})
                 \/ (corrupt_1in3_bus b bbb /\ aaa={a,a,a}).
Proof.
introv C H.
set (X:= fact_shuf1 a a a b b b).
eapply step_g_eqmodG in X; try (exact H); try (apply eq_mod_G_refl).
Apply stepg_am1fault in H. 
Inverts X. Inverts H; SimpS.
- Apply emG_pure in H7.
  Apply emG_corrupts in H3.
- Apply emG_pure in H3.
  Apply emG_corrupts in H7.
Qed.


(** *** About shuf2    *)

Lemma shuf2_corrupt1: forall S T a b c sss aaa bbb,
                       corrupt_1in3_bus1 a aaa 
                    -> corrupt_1in3_bus1 b bbb
                    -> step (shuf2 S T) {aaa,bbb} sss c
                    -> corrupt_1in3_bus1 {a,b} sss.
Proof.
introv C1 C2 H. Dd_buset_all. 
assert (X:step (shuf2 S T)  {x4, x5, x3, {x1, x2, x0}} {x4, x1, {x5, x2}, {x3, x0}} (shuf2 S T))
    by (apply fact_shuf2). 
Detstepres H X. 
Inverts C1; Inverts C2; SimpS; easy.
Qed.

Lemma shuf2_corrupt2: forall S T a b c sss aaa bbb,
                       corrupt_1in3_bus2 a aaa 
                    -> corrupt_1in3_bus2 b bbb
                    -> step (shuf2 S T) {aaa,bbb} sss c
                    -> corrupt_1in3_bus2 {a,b} sss.
Proof.
introv C1 C2 H. Dd_buset_all. 
assert (X:step (shuf2 S T)  {x4, x5, x3, {x1, x2, x0}} {x4, x1, {x5, x2}, {x3, x0}} (shuf2 S T))
    by (apply fact_shuf2). 
Detstepres H X.
Inverts C1; Inverts C2; SimpS; easy.
Qed.

Lemma shuf2_corrupt3: forall S T a b c sss aaa bbb,
                       corrupt_1in3_bus3 a aaa 
                    -> corrupt_1in3_bus3 b bbb
                    -> step (shuf2 S T) {aaa,bbb} sss c
                    -> corrupt_1in3_bus3 {a,b} sss.
Proof.
introv C1 C2 H. Dd_buset_all. 
assert (X:step (shuf2 S T)  {x4, x5, x3, {x1, x2, x0}} {x4, x1, {x5, x2}, {x3, x0}} (shuf2 S T))
    by (apply fact_shuf2). 
Detstepres H X.
Inverts C1; Inverts C2; SimpS; easy.
Qed.

Lemma stepg_shuf2 : forall S T a b s c, 
                    pure_bset {a,b}
                 -> stepg (shuf2 S T) {{a,a,a},{b,b,b}} s c
                 -> corrupt_1in3_bus {a,b} s.
Proof.
introv C H. SimpS.
set (X:= fact_shuf2 a a a b b b).
eapply step_g_eqmodG in X; try (exact H); try (apply eq_mod_G_refl).
Apply stepg_am1fault in H. 
Inverts X. Inverts H5. Inverts H; Inverts H5; SimpS.
- Apply emG_pure in H9.
  Apply emG_pure in H11.
  SimpS. easy.
- Apply emG_pure in H9.
  Apply emG_pure in H6.
  SimpS. easy.
- Apply emG_pure in H6.
  Apply emG_pure in H11.
  SimpS. easy.
Qed.


(** *** About shuf3    *)
Lemma shuf3_corrupt1: forall S a b tab a1 a2 a3 b1 b2 b3 c,
                       corrupt_1in3_bus1 {a,b} tab 
                    -> step (shuf3 S) tab {a1,a2,a3,b1,b2,b3} c
                    -> corrupt_1in3_bus1 a {a1,a2,a3} /\ corrupt_1in3_bus1 b {b1,b2,b3}.
Proof.
introv C H. Dd_buset_all. 
assert (X:step (shuf3 S)  {x3, x5, {x, x4}, {x1, x2}} {x3, x, x1, x5, x4, x2} (shuf3 S))
    by (apply fact_shuf3). 
Detstepres H X. 
Inverts C; SimpS; easy.
Qed.


Lemma shuf3_corrupt2: forall S a b tab a1 a2 a3 b1 b2 b3 c,
                       corrupt_1in3_bus2 {a,b} tab 
                    -> step (shuf3 S) tab {a1,a2,a3,b1,b2,b3} c
                    -> corrupt_1in3_bus2 a {a1,a2,a3} /\ corrupt_1in3_bus2 b {b1,b2,b3}.
Proof.
introv C H. Dd_buset_all. 
assert (X:step (shuf3 S)  {x3, x5, {x, x4}, {x1, x2}} {x3, x, x1, x5, x4, x2} (shuf3 S))
    by (apply fact_shuf3). 
Detstepres H X. Inverts X. 
Inverts C. SimpS. easy.
Qed.


Lemma shuf3_corrupt3: forall S a b tab a1 a2 a3 b1 b2 b3 c,
                       corrupt_1in3_bus3 {a,b} tab 
                    -> step (shuf3 S) tab {a1,a2,a3,b1,b2,b3} c
                    -> corrupt_1in3_bus3 a {a1,a2,a3} /\ corrupt_1in3_bus3 b {b1,b2,b3}.
Proof.
introv C H. Dd_buset_all. 
assert (X:step (shuf3 S)  {x3, x5, {x, x4}, {x1, x2}} {x3, x, x1, x5, x4, x2} (shuf3 S))
    by (apply fact_shuf3). 
Detstepres H X.
Inverts C. SimpS. easy.
Qed.

Lemma stepg_shuf3 : forall S a b a1 a2 a3 b1 b2 b3 c, 
                    pure_bset {a,b}
                 -> stepg (shuf3 S) {{a,b},{a,b},{a,b}} {{a1,a2,a3},b1,b2,b3} c
                 -> corrupt_1in3_bus {a,b} {{a1,b1},{a2,b2},{a3,b3}}.
Proof.
introv C H. SimpS.
unfold shuf3 in H. unfold shuf1 in H. unfold shuffle in H. 
Invstep H; SimpS; easy. 
Qed.

(** *** About Voter31             *)

Lemma fact1_voter31 : forall a aaa b c, corrupt_1in3_bus a aaa -> step Voter31 aaa b c -> b=a.
Proof.
introv C H. Inverts C.
- apply step1_Voter31 in H. SimpS. easy.
- apply step2_Voter31 in H. SimpS. easy.
- apply step3_Voter31 in H. SimpS. easy.
Qed.

Lemma fact2_voter31 : forall a b c, pure_bset a -> stepg Voter31 {a,a,a} b c -> b=a \/ b=(~?).
Proof.
introv T H.
assert (X: redcomb Voter31 {a,a,a}=a) by (Destruct_s a as a; destruct a; easy).
apply redcomb_imp_step in X; try (solve[repeat constructor]).
eapply step_g_eqmodG in H; try (exact X); try (apply eq_mod_G_refl).
Inverts H; Inverts T; easy.
Qed.

(** *** About Tvoter31             *)
Lemma fact1_tvoter31 : forall a aaa bbb c, 
                       corrupt_1in3_bus a aaa -> step Tvoter31 aaa bbb c 
                    -> bbb={a,a,a}.
Proof.
introv C H. unfold Tvoter31 in H. Dd_buset bbb.  
Inverts C; Invstep H; SimpS;
Apply fact1_voter31 in H1;
Apply fact1_voter31 in H2;
Apply fact1_voter31 in H3; subst; easy.
Qed.

Lemma stepg_tvoter31 : forall a b c, 
                       pure_bset a 
                    -> stepg Tvoter31 {a,a,a} b c 
                    -> corrupt_1in3_bus a b.
Proof.
introv P H. unfold Tvoter31 in H. Dd_buset b.  
Invstep H; SimpS.
- Apply fact1_voter31 in H2; 
  Apply fact1_voter31 in H5; 
  Apply fact2_voter31 in H3; subst; easy.
- Apply fact1_voter31 in H2; 
  Apply fact2_voter31 in H5; 
  Apply fact1_voter31 in H3; subst; easy.
- Apply fact2_voter31 in H2;
  Apply fact1_voter31 in H4;
  Apply fact1_voter31 in H3; subst; easy.
Qed.


Lemma  fact_irTvotshuf2 : forall S a b c x x1 x2 x3,
                    corrupt_1in3_bus x {x1,x2,x3} 
                 -> redcomb ((-| ID, (RSH) -o- (Tvoter31) |-) -o- (shuf2 S §)) 
                    {a,b,c, {x1, {x2, x3}}} = {{a, x},{b,x},{c,x}}.
Proof.
introv H.
Inverts H; try (Destruct_s x1 as x1; destruct x1);
           try (Destruct_s x2 as x2; destruct x2); 
           try (Destruct_s x3 as x3; destruct x3); cbv; reflexivity.
Qed.


(** *** About introglitch             *)

Lemma fact1_introglitch : forall S (a:{|S|}) (b:{|§|}) a1 a2 a3 b1 b2 b3, 
                          introglitch {a, a, a, b, {b, b}} {a1, a2, a3, b1, {b2, b3}}
                      -> (corrupt_1in3_bus a {a1,a2,a3} /\ {b1,b2,b3}={b,b,b})
                      \/ (corrupt_1in3_bus b {b1,b2,b3} /\ {a1,a2,a3}={a,a,a}).
Proof.
introv I. Inverts I; Inverts H;
try Inverts H0; try Inverts H1; try Inverts H0; try Inverts H; try easy. 
Qed.

Lemma fact2_introglitch : forall S (a:{|S|}) (b:{|§|}) a1 a2 a3 b1 b2 b3, 
                          introglitch {a, a, a, {b, {b, b}}} {a1, a2, a3, {b1, {b2, b3}}}
                      -> (corrupt_1in3_bus a {a1,a2,a3} /\ {b1,b2,b3}={b,b,b})
                      \/ (corrupt_1in3_bus b {b1,b2,b3} /\ {a1,a2,a3}={a,a,a}).
Proof.
introv I. Inverts I; Inverts H;
try Inverts H0; try Inverts H1; try Inverts H0; try Inverts H; try easy. 
Qed.

Lemma fact3_introglitch : forall S (a:{|S|}) bbb, 
                          introglitch {a, a, a} bbb
                      -> (corrupt_1in3_bus a bbb).
Proof.
introv I. 
Inverts I; try easy. 
Inverts H0; easy.
Qed.


(** *** About votmr             *)

Lemma fact1_votmr : forall S a b b1 b2 b3, 
                    corrupt_1in3_bus b {b1,b2,b3} -> step (votmr S) {a,a,a,b1,b2,b3} {{a,b},{a,b},{a,b}} (votmr S).
Proof.
introv C. apply redcomb_imp_step.
- repeat constructor.
- Inverts C; try (Destruct_s b1 as b1; destruct b1); 
             try (Destruct_s b2 as b2; destruct b2); 
             try (Destruct_s b3 as b3; destruct b3); cbv; reflexivity. 
Qed.

Lemma fact2_votmr : forall S a b s c, 
                    pure_bset {a,b}
                 -> stepg (votmr S) {a,a,a,b,b,b} s c
                 -> corrupt_1in3_bus {a,b} s.
Proof.
introv P H. unfold votmr in H.
Invstep H. SimpS.
Apply stepg_tvoter31 in H7.
Inverts H7.
- assert (X:step (shuf2 S §)  {a, a, a, {x5, x5, x3}} {a, x5, {a,x5}, {a, x3}} (shuf2 S §))
      by (apply fact_shuf2). 
  Detstepres H2 X. SimpS. easy.
- assert (X:step (shuf2 S §)  {a, a, a, {x3, x5, x3}} {a, x3, {a,x5}, {a, x3}} (shuf2 S §))
      by (apply fact_shuf2). 
  Detstepres H2 X. SimpS. easy.
- assert (X:step (shuf2 S §)  {a, a, a, {x4, x3, x3}} {a, x4, {a,x3}, {a, x3}} (shuf2 S §))
      by (apply fact_shuf2). 
  Detstepres H2 X. SimpS. easy.
Qed.
