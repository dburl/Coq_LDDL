(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        The double time redundancy (DTR) transformation   
#</h1>#    
- Inversion lemmas for DTR transformation
#</center> <hr>#                                           
          Dmitry Burlyaev - Pascal Fradet - 2015           *)
(* ------------------------------------------------------- *)

Add LoadPath "..\..\Common\".
Add LoadPath "..\..\TMRProof\".
Add LoadPath "..\Transf\".

Require Import dtrTransform.

Set Implicit Arguments.

(* ------------------------------------------------------- *)

Lemma invIG1 : forall (a1 a2 a3 a4 a5 b1 b2 b3 b4 b5:{|§|}),
               introglitch {b1,b2,b3,b4,b5} {a1,a2,a3,a4,a5} 
            -> (a1=b1   /\ a2=b2   /\ a3=b3   /\ a4=b4   /\ a5=b5)
            \/ (a1=(~?) /\ a2=b2   /\ a3=b3   /\ a4=b4   /\ a5=b5)
            \/ (a1=b1   /\ a2=(~?) /\ a3=b3   /\ a4=b4   /\ a5=b5)
            \/ (a1=b1   /\ a2=b2   /\ a3=(~?) /\ a4=b4   /\ a5=b5)
            \/ (a1=b1   /\ a2=b2   /\ a3=b3   /\ a4=(~?) /\ a5=b5)
            \/ (a1=b1   /\ a2=b2   /\ a3=b3   /\ a4=b4   /\ a5=(~?)).
Proof.
introv H. 
repeat match goal with 
| [H:{_,_} = {_,_} |- _] => Inverts H
| [H: introglitch _ _ |- _] => Inverts H
end; try (solve[left;easy]); try (solve[right;left;easy]);
     try (solve[right;right;left;easy]); try (solve[right;right;right;left;easy]);
     try (solve[right; right;right;right;left;easy]);try (solve[right; right;right;right;right;easy]).
Qed.

Definition PexInvDTR1 S T s t f1 f2 f3  
                      (c1 :circuit (S # §) S)
                      (c2 :circuit (§ # § # §) (§ # §# § # § # §))
                      (c3 :circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)))
                      (c4 :circuit (T # (§ # § # § # §)) (T # (T # T) # §))
                      (c' : circuit (((S # §) # §) # §) ((((T # (T # T)) # §) # §) # §))
           := exists t1 s1 s2 s3 s4 s5 a1 a2 a3 a4,
              exists r1 r2 r3 r4,
              exists c'1 c'2 c'3 c'4,
                     step c1 {s, s1} t1 c'1
                  /\ step c2 {f1,f2,f3} {s2, s4, s3, s1, s5} c'2
                  /\ step c3 {t1, {s2, s4, s3}} {a1, {a2, a3, a4}} c'3
                  /\ step c4 {a1, {a2, a3, a4, s5}} {r1, {r2, r3}, r4} c'4
                  /\ t = {r1, {r2, r3},r4,r4,r4}
                  /\ c'= dtrcore c'1 c'2 c'3 c'4.


Definition PexInvDTR2 S T s t f1 f2 f3  
                      (c1 :circuit (S # §) S)
                      (c2 :circuit (§ # § # §) (§ # §# § # § # §))
                      (c3 :circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)))
                      (c4 :circuit (T # (§ # § # § # §)) (T # (T # T) # §))
                      (c' : circuit (((S # §) # §) # §) ((((T # (T # T)) # §) # §) # §))
           := exists t1 s1 s2 s3 s4 s5 a1 a2 a3 a4,
              exists r1 r2 r3 r4,
              exists c'1 c'2 c'3 c'4,
                     step c1 {s, s1} t1 c'1
                  /\ stepg c2 {f1,f2,f3} {s2, s4, s3, s1, s5} c'2
                  /\ step c3 {t1, {s2, s4, s3}} {a1, {a2, a3, a4}} c'3
                  /\ step c4 {a1, {a2, a3, a4, s5}} {r1, {r2, r3}, r4} c'4
                  /\ t = {r1, {r2, r3},r4,r4,r4}
                  /\ c'= dtrcore c'1 c'2 c'3 c'4.                

Definition PexInvDTR3 S T s t f1 f2 f3  
                      (c1 :circuit (S # §) S)
                      (c2 :circuit (§ # § # §) (§ # §# § # § # §))
                      (c3 :circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)))
                      (c4 :circuit (T # (§ # § # § # §)) (T # (T # T) # §))
                      (c' : circuit (((S # §) # §) # §) ((((T # (T # T)) # §) # §) # §))
           := exists t1 s1 s2 s3 s4 s5 a1 a2 a3 a4,
              exists r1 r2 r3 r4,
              exists c'1 c'2 c'3 c'4,
                     stepg c1 {s, s1} t1 c'1
                  /\ step c2 {f1,f2,f3} {s2, s4, s3, s1, s5} c'2
                  /\ step c3 {t1, {s2, s4, s3}} {a1, {a2, a3, a4}} c'3
                  /\ step c4 {a1, {a2, a3, a4, s5}} {r1, {r2, r3}, r4} c'4
                  /\ t = {r1, {r2, r3},r4,r4,r4}
                  /\ c'= dtrcore c'1 c'2 c'3 c'4.


Definition PexInvDTR4 S T s t f1 f2 f3  
                      (c1 :circuit (S # §) S)
                      (c2 :circuit (§ # § # §) (§ # §# § # § # §))
                      (c3 :circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)))
                      (c4 :circuit (T # (§ # § # § # §)) (T # (T # T) # §))
                      (c' : circuit (((S # §) # §) # §) ((((T # (T # T)) # §) # §) # §))
           := exists t1 s1 s2 s3 s4 s5 a1 a2 a3 a4,
              exists r1 r2 r3 r4,
              exists c'1 c'2 c'3 c'4,
                     step c1 {s, s1} t1 c'1
                  /\ step c2 {f1, f2, f3} {s2, s4, s3, s1, s5} c'2
                  /\ stepg c3 {t1, {s2, s4, s3}} {a1, {a2, a3, a4}} c'3
                  /\ step c4 {a1, {a2, a3, a4, s5}} {r1, {r2, r3}, r4} c'4
                  /\ t = {r1, {r2, r3},r4,r4,r4}
                  /\ c'= dtrcore c'1 c'2 c'3 c'4.


Definition PexInvDTR5 S T s t f1 f2 f3  
                      (c1 :circuit (S # §) S)
                      (c2 :circuit (§ # § # §) (§ # §# § # § # §))
                      (c3 :circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)))
                      (c4 :circuit (T # (§ # § # § # §)) (T # (T # T) # §))
                      (c' : circuit (((S # §) # §) # §) ((((T # (T # T)) # §) # §) # §))
           := exists t1 s1 s2 s3 s4 s5 a1 a2 a3 a4,
              exists r1 r2 r3 r4,
              exists c'1 c'2 c'3 c'4,
                     step c1 {s, s1} t1 c'1
                  /\ step c2 {f1, f2, f3} {s2, s4, s3, s1, s5} c'2
                  /\ step c3 {t1, {s2, s4, s3}} {a1, {a2, a3, a4}} c'3
                  /\ stepg c4 {a1, {a2, a3, a4, s5}} {r1, {r2, r3}, r4} c'4
                  /\ t = {r1, {r2, r3},r4,r4,r4}
                  /\ c'= dtrcore c'1 c'2 c'3 c'4.



Lemma invstepcore : forall S T f1 f2 f3 s t 
                      (c1 :circuit (S # §) S)
                      (c2 :circuit (§ # § # §) (§ # §# § # § # §))
                      (c3 :circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)))
                      (c4 :circuit (T # (§ # § # § # §)) (T # (T # T) # §))
                      (c' : circuit (((S # §) # §) # §) ((((T # (T # T)) # §) # §) # §)),
                  pure_bset s 
               -> step (dtrcore c1 c2 c3 c4) {s,f1, f2, f3} t c' 
               -> PexInvDTR1 s t f1 f2 f3 c1 c2 c3 c4 c'.
Proof.  
introv P H. 
unfold dtrcore in H. Invstep H. SimpS. 
unfold PexInvDTR1. 
exists x99 x58 x60 x59 x61 x57.
exists x40 x42 x43 x41.
exists x37 x38 x39 x6.
exists x95 x79 x97 x83.
repeat split; try easy.
Qed. 


Lemma invstepDTRc : forall S T f1 f2 f3 i1 i2 o1 o2 o3 o4 o5 s t 
                           cbc (c:circuit (S # ((§ # §) # §)) (T # ((§ # §) # §))) 
                           (c': circuit S (T # (T # T))),
                   pure_bset {o1,o2,o3,o4,o5,i1,i2,s} 
                -> step (-{f1}- (-{f2}- (-{f3}- 
                        (dtrcore (dtrIB_T i1 i2) cbc c (dtrOB_T o1 o2 o3 o4 o5)))))
                         s t c' 
                -> exists t1 s1 s2 s3 s4 s5 a1 a2 a3 a4,
                   exists f r1 r2 r3 r4,
                   exists c1 c2 c3 c4,
                   step (dtrIB_T i1 i2) {s, s1} t1 c1
                /\ step cbc {bool2bset f1, bool2bset f2, bool2bset f3}
                                                {s2, s4, s3, s1, s5} c2
                /\ step c {t1, {s2, s4, s3}} {a1, {a2, a3, a4}} c3
                /\ step (dtrOB_T o1 o2 o3 o4 o5) {a1, {a2, a3, a4, s5}}
                                                   {r1, {r2, r3}, r4} c4
                /\ bset2bool r4 f
                /\ t = {r1, {r2, r3}}
                /\ c'= (-{f}-(-{f}- (-{f}- (dtrcore c1 c2 c3 c4))))
                /\ pure_bset {s1,s2,s3,s4,s5,a1,a2,a3,a4,r1,r2,r3,r4,t1}.
Proof. 
introv P H. 
unfold dtrcore in H. Invstep H. SimpS. 
Purestep H26. SimpS. Purestep H21. SimpS.
Purestep H22. SimpS. Purestep H13. SimpS.
exists x105 x58 x60 x59 x61 x57.
exists x40 x42 x43 x41.
exists x75 x37 x38 x39 x36.
exists x101 x84 x103 x88.
repeat split; try easy.
CheckPure.
Qed.

Lemma invstepgcore : forall S T f1 f2 f3 s t 
                      (c1 :circuit (S # §) S)
                      (c2 :circuit (§ # § # §) (§ # §# § # § # §))
                      (c3 :circuit (S # ((§ # §) # §)) (T # ((§ # §) # §)))
                      (c4 :circuit (T # (§ # § # § # §)) (T # (T # T) # §))
                      (c' : circuit (((S # §) # §) # §) ((((T # (T # T)) # §) # §) # §)),
                     pure_bset s 
                  -> stepg (dtrcore c1 c2 c3 c4) {s,f1, f2, f3} t c' 
                  -> PexInvDTR2 s t f1 f2 f3 c1 c2 c3 c4 c' 
                  \/ PexInvDTR3 s t f1 f2 f3 c1 c2 c3 c4 c' 
                  \/ PexInvDTR4 s t f1 f2 f3 c1 c2 c3 c4 c'
                  \/ PexInvDTR5 s t f1 f2 f3 c1 c2 c3 c4 c'. 

Proof. 
introv P H.
unfold dtrcore in H.
Invstep H.
- left. SimpS.
  exists x88 x2 x1 x3 x4 x0. 
  exists x40 x42 x43 x41.
  exists x37 x38 x39 x18.
  exists x84 x14 x86 x72.
  repeat split; easy.
- right; left. SimpS.
  exists x x35 x37 x36 x38 x34.
  exists x21 x16 x17 x15.
  exists x46 x48 x49 x56.
  exists x55 x51 x54 x52.
  repeat split; easy.
- right. right. left. SimpS.
  exists x54 x35 x37 x36 x38 x34. 
  exists x18 x13 x14 x12.
  exists x43 x44 x45 x51.
  exists x50 x48 x52 x49.
  repeat split; easy.
- right. right. right. SimpS.
  exists x52 x41 x43 x42 x44 x40.
  exists x29 x31 x32 x30.
  exists x14 x15 x16 x2.
  exists x51 x49 x50 x8.
  repeat split; easy.
Qed.

