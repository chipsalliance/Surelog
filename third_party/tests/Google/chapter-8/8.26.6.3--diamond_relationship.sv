/*
:name: diamond_relationship
:description: interface class inherited from multiple sources shouldn't create symbol conflicts
:tags: 8.26.6.3
*/
module class_tb ();
	interface class ibase;
		pure virtual function void fn();
	endclass

	interface class ic1 extends ibase;
		pure virtual function void fn1();
	endclass

	interface class ic2 extends ibase;
		pure virtual function void fn2();
	endclass
	
	interface class ic3 extends ic1, ic2;
		pure virtual function void fn3();
	endclass
endmodule
