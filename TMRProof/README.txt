
This folder gathers the files proving the triple modular redundancy transformation (TMR).
The transformation triplicates the whole circuit and inserts a triplicated voter after 
each triplicated cell. It tolerates a glitch every two cycles (ie. the fault-model denoted SET(1,2))

It imports the basic definitions and properties of the syntax and semantics
of the hardware description language (Common folder, CirReflect.v file).

The main tactics used are defined in LibTactics.v (from UPenn Software Foundation)
and CirTactics. The most used are :

- introv (introduces all variables and uses names for hypotheses)
- easy (tries to conclude with simpl and auto)
- SimpS (destruct and simplifies all hypotheses (not disjunctions))
- CheckPure  checks the purity of a bus 
- PureStep, Rdet apply determinism lemmas to infer equalities between buses
- Apply L with H1 H2 ... (in H) (applies L to goal or H and tries "exact Hi", CheckPure and easy)


The files are :

- tmrDef    : describes the TMR transformation and relation between states of source and transformed circuits
- tmrPlugs  : lemmas about the plugs and basic constituents used in the transformation
- tmrMainTh : expresses the main correctness property and proves it.

make.bat triggers the compilation in the correct order (it should take around 5-10 minutes).