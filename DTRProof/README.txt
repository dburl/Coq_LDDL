
This folder gathers the files proving the double time redundancy (DTR) transformation.
The transformation performs: 
	1) substitution of each original memory cell with a memory
		block and threading of control wires within the circuit;
	2) addition of a control block;
	3) addition of input buffers to all circuit primary inputs;
	4) addition of output buffers to all circuit primary outputs.

It tolerates an SET if it happens less frequently than every 10 clock cycles (i.e. the fault-model is SET(1,10))

We have to import the basic definitions and properties of the syntax and semantics
of the hardware description language (Common folder, CirReflect.v file). In addition, DTR  uses TMR
transformation and  properties.
So, DTR folder has to be located in the same directory as TMR folder.


The main tactics used are defined in LibTactics.v (from UPenn Software Foundation), Utils.v
and CirTactics.v. The most often used are :

	- introv (introduces all variables and uses names for hypotheses);
	- easy (tries to solve the goal with simpl and auto)
	- Inverts that performs an inversion dealing with dependent types (without relying on any axioms);
	- Destruct_s (and similar) that perform a dependent detruction of buses (gates, plugs, circuits) without relying on JMeq axiom);
	- SimpS (destruct and simplifies all hypotheses (not disjunctions));
	- CheckPure checks the purity of a bus;
	- PureStep, Rdet apply determinism lemmas to infer equalities between buses;
	- Apply L with H1 H2 ... (in H) (applies L to goal or H and tries "exact Hi", CheckPure and easy).


The main file is mainTheorem which expresses the main correctness property and proves it.

Subfolders contain the lemmas and their proofs about DTR sub-parts. The folder names identify the corresponding DTR 
sub-circuit. 
The folder /Transf specifies the DTR transformation and /globalCircuit provides properties of the whole DTR transformation.

We follow the naming convention in each of these folders:
If xxx_ is the name of DTR sub-part (eg memory for memory blocks, control for control block, etc.), then
	xxx_Rec file - contains properties during the recovery process for the sub-part xxx_;
	xxx_Step file- contains properties during the normal execution (without SETs) for the sub-part xxx_;
		xxx_Step0 file-  contains properties for even clock cycles without SETs
		xxx_Step1 file-  contains properties for odd clock cycles without SETs
	xxx_Stepg file- contains properties when SET occurs for the sub-part xxx_		
		xxx_Stepg0 and xxx_Stepg1 – for even and odd cycles with SETs correspondingly
	xxx_Lib file - imports all needed properties and is created for the convenient hierarchical organization of the overall proof
			(for inputBuffers it's a single file that gathers all properties since there are not a lot of them)
	xxx_Inv0 and xxx_Inv1 - contain supporting intermediate lemmas about structural decomposition of big circuits 
			(eg memory blocks) into smaller sub-components. These lemmas are outsourced to make easier
 			the proofs where such decomposition is needed.

memoryBlock folder contains files where xxx_ are “left” and “right”. These files define properties for memory block sub-parts. 	

makeall.bat triggers the compilation in the correct order (it should take around 30-40 minutes) of the whole DTR project.
