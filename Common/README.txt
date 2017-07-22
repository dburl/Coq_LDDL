
This folder gathers the files defining buses, signals and the syntax and semantics of LDDL, a gate-level core hardware description language.
It provides also utilities to performs proof by reflection and basic tactics for LDDL.

The files are :
- LibTactics : library of tactics borrowed from UPenn (we use introv, exists, false, ...)
- Utils      : a few simple tactics (easy, etc.)
- Signals    : describes bus, signals
- Syntax     : of LDDL and a few small circuits
- Semantics  : of LDDL (relational, functional, for 1 cycle, for infinite streams)
- PropSem    : basic lemmas on the semantics
- PropSub    : properties of some small circuits (Mux, voter, ...)
- CirTactics : collection of tactics for proving properties of LDDL (SimpS, CheckPure, PureStep, Rdet, Apply, ...)
- CirReflect : properties and lemmas to facilitate proof by reflection of LDDL.

make.bat triggers the compilation in the correct order.