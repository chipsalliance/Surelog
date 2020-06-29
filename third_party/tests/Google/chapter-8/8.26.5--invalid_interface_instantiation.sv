/*
:name: interface_instantiation
:description: instantiating an interface class
:should_fail_because: interface class cannot be instantiated
:tags: 8.26.5
:type: simulation
*/
module class_tb ();
	interface class ihello;
		pure virtual function void hello();
	endclass
	
	ihello obj;

	initial begin
		obj = new;
	end
endmodule
