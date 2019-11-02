/*
:name: interface_instantiation
:description: instantiating an interface class
:should_fail: 1
:tags: 8.26.5
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
