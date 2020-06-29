/*
:name: diamond_relationship_parametrized
:description: different specializations of an interface class
:should_fail_because: different specializations of an interface class are treated as unique interface class types
:tags: 8.26.6.3
:type: simulation
*/
module class_tb ();
	interface class ibase#(type T = logic);
		pure virtual function void fn(T val);
	endclass

	interface class ic1 extends ibase#(bit);
		pure virtual function void fn1();
	endclass

	interface class ic2 extends ibase#(string);
		pure virtual function void fn2();
	endclass
	
	interface class ic3 extends ic1, ic2;
		pure virtual function void fn3();
	endclass
endmodule
