/*
:name: name_conflict_unresolved
:description: unresolved interface class method name conflict
:should_fail_because: in this test it's unclear which interface is hello() part of
:tags: 8.26.6.1
:type: simulation
*/
module class_tb ();
	interface class ihello;
		pure virtual function void hello();
	endclass

	interface class itest;
		pure virtual function int hello();
	endclass
	
	class Hello implements ihello, itest;
		virtual function void hello();
			$display("hello world");
		endfunction
	endclass

	Hello obj;

	initial begin
		obj = new;
		obj.hello();
	end
endmodule
