/*
:name: parameter_type_conflict_unresolved
:description: superclass type declaration conflicts must be resolved in subclass
:should_fail_because: the parameter T is inherited from both classess and creates a conflict 
:tags: 8.26.6.2
:type: simulation
*/
module class_tb ();
	interface class ic1#(type T = logic);
		pure virtual function void fn1(T a);
	endclass

	interface class ic2#(type T = logic);
		pure virtual function void fn2(T a);
	endclass
	
	interface class ic3#(type TYPE = logic) extends ic1#(TYPE), ic2#(TYPE);
	endclass
endmodule
