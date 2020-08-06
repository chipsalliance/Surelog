/*
:name: implements_multiple
:description: class implementing multiple interfaces
:tags: 8.26.2
*/
module class_tb ();
	interface class ihello;
		pure virtual function void hello();
	endclass

	interface class itest;
		pure virtual function void test();
	endclass
	
	class Hello implements ihello, itest;
		virtual function void hello();
			$display("hello world");
		endfunction
		virtual function void test();
			$display("test");
		endfunction
	endclass

	Hello obj;

	initial begin
		obj = new;
		obj.hello();
		obj.test();
	end
endmodule
