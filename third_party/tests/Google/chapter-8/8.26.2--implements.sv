/*
:name: implements
:description: implements keyword test
:tags: 8.26.2
*/
module class_tb ();
	interface class ihello;
		pure virtual function void hello();
	endclass
	
	class Hello implements ihello;
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
