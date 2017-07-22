(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The triple modular redundancy transformation   
#</h1>#    
-   Inversion lemmas (computationnally costly)

              Pascal Fradet - Inria - 2014  
#</center> <hr>#                                           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\Common\".

Require Export ttrCMBlocks.

Set Implicit Arguments.


(** Inversion theorems for step reduction of TTR transformed circuits *)


Lemma invstepTTRpar : forall S T U V x1 x2 x3 x4 fA fB s 
                       (c31 : circuit (S # (§ # §)) (T # (§ # §)))
                       (c32 : circuit (U # (§ # §)) (V # (§ # §)))
                       (d   : circuit ((S # U) # (§ # §)) ((T # V) # (§ # §))), 
                 step ((SWAP_LR S U (§ # §)) -o- (((-| c31, ID |-) -o- (SWAP_LS T (§ # §) U)) -o-
                      (-| ID, c32 |- -o- RSH))) {s, {fA,fB}} {x1, x2, {x3, x4}} d
                     -> exists c31' c32' y1 y2, 
                        d = LSH -o- (-| ID, SWAP |- -o- RSH) -o-
                            (((-| c31', ID |-) -o- (LSH -o- -| ID, SWAP |-)) -o-
                            (-| ID, c32' |- -o- RSH)) 
                     /\ step c31 {fstS s, {fA,fB}} {x1, {y1, y2}} c31'
                     /\ step c32 {sndS s, {y1,y2}} {x2, {x3, x4}} c32'.
Proof.
introv H.
unfold SWAP_LR in H. unfold SWAP_LS in H. Invstep H. SimpS.
exists x19 x40 x13 x14. easy.
Qed.

Lemma invstepTTRloop : forall S T d1 d2 d3 kA kB fA fB s t1 t2 t3 
                       (c : circuit ((S # §) # (§ # §)) ((T # §) # (§ # §)))
                       (d : circuit (S # (§ # §)) (T # (§ # §))), 
                 step (-{d1}- ((SWAP_LS S (§ # §) §)-o- -| ID, mb_ttr d2 d3 kA kB |- -o-
                               RSH-o- c -o- (SWAP_LR T § (§ # §)))) {s, {fA, fB}} {t1,{t2,t3}} d
                     -> exists c31 c32 x1 x2 x3 y z, 
                        d = -{z}- (LSH -o- -| ID, SWAP |-) -o- (-| ID, c32 |- -o-
                                    RSH -o- c31 -o-  LSH -o- -| ID, SWAP |- -o- RSH)   
                     /\ bset2bool y z
                     /\ step c {s, x1, {x2, x3}} {t1, y, {t2, t3}}  c31
                     /\ step (mb_ttr d2 d3 kA kB) {bool2bset d1, {fA,fB}} {x1, {x2, x3}} c32.
Proof.
introv H.
unfold SWAP_LR in H. unfold SWAP_LS in H. 
Invstep H. SimpS.
exists x34 x36 x20 x21 x22.
exists x18 x28. easy.
Qed.

(** Inversion theorems for stepg of TTR transformed circuits *)

Lemma invstepgTTRpar : forall S T U V s1 s2 t1 t2 fAB fAB' 
                       (c31 : circuit (S # (§ # §)) (T # (§ # §)))
                       (c32 : circuit (U # (§ # §)) (V # (§ # §)))
                       (c'   : circuit ((S # U) # (§ # §)) ((T # V) # (§ # §))), 
                 stepg ((SWAP_LR S U (§ # §)) -o- (((-| c31, ID |-) -o- (SWAP_LS T (§ # §) U)) -o-
                      (-| ID, c32 |- -o- RSH))) {s1, s2, fAB} {t1,t2,fAB'} c'
                     -> (exists fAB1 c31' c32', stepg c31 {s1, fAB} {t1,fAB1}  c31'
                           /\ step  c32 {s2, fAB1} {t2,fAB'} c32'
                           /\ c'=((SWAP_LR S U (§ # §)) -o- (((-| c31', ID |-) 
                                    -o- (SWAP_LS T (§ # §) U)) -o- (-| ID, c32' |- -o- RSH))))
                     \/ (exists fAB1 c31' c32', step  c31 {s1, fAB} {t1,fAB1} c31'
                             /\ stepg c32 {s2, fAB1} {t2,fAB'} c32'
                             /\ c'=((SWAP_LR S U (§ # §)) -o- (((-| c31', ID |-) 
                                    -o- (SWAP_LS T (§ # §) U)) -o- (-| ID, c32' |- -o- RSH)))).
Proof.
introv H. unfold SWAP_LR in H. unfold SWAP_LS in H. 
Invstep H; SimpS.
- left. exists {x1, x2} x11 x24. easy.
- right. exists {x9, x10} x19 x22. easy.
Qed.

Lemma invstepgTTRloop0 : forall S T d k s t fAB' 
                   (c : circuit ((S # §) # (§ # §)) ((T # §) # (§ # §)))
                   (c' : circuit (S # (§ # §)) (T # (§ # §))),  
                   stepg (-{d}- (SWAP_LS S (§ # §) §) -o-  ((-| ID, mb_ttr d d k k |-) -o-
                         (((RSH) -o- (c)) -o- (SWAP_LR T § (§ # §))))) {s,{~1,~1}} {t,fAB'} c'
                -> (exists x b c1, stepg c {s, bool2bset d, {~1,~1}} {t, x, fAB'} c1
                                /\ c'= (-{b}- (SWAP_LS S (§ # §) §) -o-  ((-| ID, mb_ttr d d d d |-) -o-
                                       (((RSH) -o- (c1)) -o- (SWAP_LR T § (§ # §)))))
                                /\ bset2bool x b)
                \/ (exists x b z c1 c2, step c {s, bool2bset d, {~1,~1}} {t, x, fAB'} c1
                                    /\  c'= (-{b}- (SWAP_LS S (§ # §) §) -o-  ((-| ID, c2 |-) -o-
                                       (((RSH) -o- (c1)) -o- (SWAP_LR T § (§ # §)))))
                                    /\ bset2bool x b 
                                    /\ (c2=mb_ttr z d d d \/ c2=mb_ttr d z d d \/ c2=mb_ttr d d d z))
                \/ (exists x y b z c1, step c {s, y, {~1,~1}} {t, x, fAB'} c1
                                    /\ bset2bool x b
                                    /\  c'= (-{b}- (SWAP_LS S (§ # §) §) -o-  ((-| ID, mb_ttr d d z d |-) -o-
                                            (((RSH) -o- (c1)) -o- (SWAP_LR T § (§ # §)))))).
Proof.
introv H.
unfold SWAP_LR in H. unfold SWAP_LS in H. 
Invstep H; SimpS.
- right.
  Apply stepg_mb_ttr0 in H1; try apply s2bob2s; Simpl.
  destruct H1 as [[z [X Y]] | [[z [X Y]] | [[z [X Y]]|[z [X Y]]]]]; SimpS.
  + left. exists x14 x24 z x28 (mb_ttr d d d z). 
    split; easy.
  + left. exists x14 x24 z x28 (mb_ttr d z d d).
    split; easy. 
  + left. exists x14 x24 z x28 (mb_ttr z d d d).
    split; easy.
  + right. exists x14 x x24 z x28.
    split; easy.
- left. 
  apply step0_mb_ttr1 in H4. destruct H4 as [X [b' [? ?]]].
  SimpS. exists x11 x19 x22. easy.
- right. 
  apply step0_mb_ttr1 in H10. destruct H10 as [X [z [B ?]]]. 
  SimpS. left.
  exists x18 x29 z x35 (mb_ttr z d d d). SimpS. easy.
Qed.


Lemma invstepgTTRloop1 : forall S T d k s t fAB' 
                   (c : circuit ((S # §) # (§ # §)) ((T # §) # (§ # §)))
                   (c' : circuit (S # (§ # §)) (T # (§ # §))),  
                   stepg (-{k}- (SWAP_LS S (§ # §) §) -o-  ((-| ID, mb_ttr d d d d |-) -o-
                         (((RSH) -o- (c)) -o- (SWAP_LR T § (§ # §))))) {s,{~0,~0}} {t,fAB'} c'
                -> (exists x b c1, stepg c {s, bool2bset d, {~0,~0}} {t, x, fAB'} c1
                                /\ c'= (-{b}- (SWAP_LS S (§ # §) §) -o-  ((-| ID, mb_ttr k d d d |-) -o-
                                       (((RSH) -o- (c1)) -o- (SWAP_LR T § (§ # §)))))
                                /\ bset2bool x b)
                \/ (exists x b z c1 c2, step c {s, bool2bset d, {~0,~0}} {t, x, fAB'} c1
                                    /\  c'= (-{b}- (SWAP_LS S (§ # §) §) -o-  ((-| ID, c2 |-) -o-
                                       (((RSH) -o- (c1)) -o- (SWAP_LR T § (§ # §)))))
                                    /\ bset2bool x b 
                                    /\ (c2=mb_ttr z d d d \/ c2=mb_ttr k z d d \/ c2=mb_ttr k d d z))
                \/ (exists x y b z c1, step c {s, y, {~0,~0}} {t, x, fAB'} c1
                                    /\ bset2bool x b
                                    /\  c'= (-{b}- (SWAP_LS S (§ # §) §) -o-  ((-| ID, mb_ttr k d z d |-) -o-
                                            (((RSH) -o- (c1)) -o- (SWAP_LR T § (§ # §)))))).
Proof.
introv H.
unfold SWAP_LR in H. unfold SWAP_LS in H. 
Invstep H; SimpS.
- right. 
  apply stepg_mb_ttr1 with (dd:=k) (b:=bool2bset d) in H1; 
        try CheckPure; try apply s2bob2s; try easy.
  destruct H1 as [[z [X Y]] | [[z [X Y]] | [[z [X Y]]|[z [X Y]]]]]; SimpS.
  + left. exists x14 x24 z x28 (mb_ttr k d d z). 
    split; easy.
  + left. exists x14 x24 z x28 (mb_ttr k z d d).
    split; easy. 
  + left. exists x14 x24 z x28 (mb_ttr z d d d).
    split; easy.
  + right. exists x14 x x24 z x28.
    split; easy.
- left. apply step1_mb_ttr1 in H4; SimpS. 
  exists x11 x19 x22. easy.
- right. left.
  apply step1_mb_ttr1 in H10.
  destruct H10 as [X [z [B ?]]]. 
  exists x18 x29 z x35 (mb_ttr z d d d). SimpS; easy. 
Qed.

Lemma invstepgTTRloop2 : forall S T d k s t fAB' 
                   (c : circuit ((S # §) # (§ # §)) ((T # §) # (§ # §)))
                   (c' : circuit (S # (§ # §)) (T # (§ # §))),  
                   stepg (-{k}- (SWAP_LS S (§ # §) §) -o-  ((-| ID, mb_ttr k d d d |-) -o-
                         (((RSH) -o- (c)) -o- (SWAP_LR T § (§ # §))))) {s,{~0,~0}} {t,fAB'} c'
                -> (exists x b c1, stepg c {s, bool2bset d, {~0,~0}} {t, x, fAB'} c1
                                /\ c'= (-{b}- (SWAP_LS S (§ # §) §) -o-  ((-| ID, mb_ttr k k d d |-) -o-
                                       (((RSH) -o- (c1)) -o- (SWAP_LR T § (§ # §)))))
                                /\ bset2bool x b)
                \/ (exists x b z c1 c2, step c {s, bool2bset d, {~0,~0}} {t, x, fAB'} c1
                                    /\  c'= (-{b}- (SWAP_LS S (§ # §) §) -o-  ((-| ID, c2 |-) -o-
                                       (((RSH) -o- (c1)) -o- (SWAP_LR T § (§ # §)))))
                                    /\ bset2bool x b 
                                    /\ (c2=mb_ttr z k d d \/ c2=mb_ttr k z d d \/ c2=mb_ttr k k d z))
                \/ (exists x y b z c1, step c {s, y, {~0,~0}} {t, x, fAB'} c1
                                    /\ bset2bool x b
                                    /\  c'= (-{b}- (SWAP_LS S (§ # §) §) -o-  ((-| ID, mb_ttr k k z d |-) -o-
                                            (((RSH) -o- (c1)) -o- (SWAP_LR T § (§ # §)))))).
Proof.
introv H. unfold SWAP_LR in H. unfold SWAP_LS in H. 
Invstep H; SimpS.
- right. 
  apply stepg_mb_ttr2 with (dd:=k) (b:=bool2bset d) in H1;
  try apply b2t_is_pure; try apply s2bob2s; try easy. 
  destruct H1 as [[z [X Y]] | [[z [X Y]] | [[z [X Y]]|[z [X Y]]]]]; SimpS.
  + left. exists x14 x24 z x28 (mb_ttr k k d z).
    split; easy.
  + left. exists x14 x24 z x28 (mb_ttr k z d d).
    split; easy. 
  + left. exists x14 x24 z x28 (mb_ttr z k d d).
    split; easy.  
  + right. exists x14 x x24 z x28. easy.
- left.
  apply step1_mb_ttr1 in H4; SimpS.
  exists x11 x19 x22. easy.
- right. left.
  apply step1_mb_ttr1 in H10. destruct H10 as [X [z [B ?]]]. 
  exists x18 x29 z x35 (mb_ttr z k d d).
  SimpS. easy. 
Qed.


