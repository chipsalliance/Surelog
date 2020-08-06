/*
:name: name_conflict_resolved
:description: resolved interface class method name conflict
:tags: 8.26.6.1
:type: simulation parsing
*/
module class_tb ();
	interface class ihello;
		pure virtual function void hello();
	endclass

	interface class itest;
		pure virtual function void hello();
	endclass
	
	class Hello implements ihello, itest;
		virtual function void hello();
			$display(":assert:(True)");
		endfunction
	endclass

	Hello obj;

	initial begin
		obj = new;
		obj.hello();
	end
endmodule
