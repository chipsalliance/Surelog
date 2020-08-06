/*
:name: implemented_class_handle
:description: it should be possible to assign object handle to a variable of an implemented class type
:tags: 8.26.5
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
	ihello iobj;

	initial begin
		obj = new;
		iobj = obj;
	end
endmodule
