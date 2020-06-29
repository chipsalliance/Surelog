/*
:name: illegal_implements_parameter
:description: implementing parameter of interface class
:should_fail_because: implementing parameter that resolves to an interface class is not allowed
:tags: 8.26.4
:type: simulation
*/
module class_tb ();
	interface class ihello;
		typedef int int_t;
		pure virtual function void hello(int_t val);
	endclass

	class Hello #(type T = ihello) implements T;
		virtual function void hello(ihello::int_t val);
			$display("hello world %d", val);
		endfunction
	endclass

	Hello obj;

	initial begin
		obj = new;
		obj.hello();
	end
endmodule
