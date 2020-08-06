/*
:name: partial_implementation
:description: virtual classes can implement their interfaces partially
:tags: 8.26.7
*/
module class_tb ();
	interface class ihello;
		pure virtual function void hello();
		pure virtual function void world();
	endclass

	virtual class vhello implements ihello;
		virtual function void hello();
			$display("hello");
		endfunction
		pure virtual function void world();
	endclass

	class helloworld extends vhello;
		virtual function void world();
			$display("world");
		endfunction
	endclass

	helloworld obj;

	initial begin
		obj = new;

		obj.hello();
		obj.world();
	end
endmodule
