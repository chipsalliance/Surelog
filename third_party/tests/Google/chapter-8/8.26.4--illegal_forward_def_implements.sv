/*
:name: illegal_forward_def_implements
:description: implementing typedef for an interface class
:should_fail_because: implementing forward typedef for an interface class should fail
:tags: 8.26.4
:type: simulation
*/
module class_tb ();
	typedef interface class ihello;

	class Hello implements ihello;
		virtual function void hello(ihello::int_t val);
			$display("hello world %d", val);
		endfunction
	endclass

	interface class ihello;
		typedef int int_t;
		pure virtual function void hello(int_t val);
	endclass

	Hello obj;

	initial begin
		obj = new;
		obj.hello();
	end
endmodule
