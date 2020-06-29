/*
:name: constructor
:description: class constructor test
:tags: 8.7
:type: simulation parsing
*/
module class_tb ();
	class test_cls;
		int a;
		function new();
			a = 42;
		endfunction
	endclass

	initial begin
		test_cls test_obj = new;

		$display(":assert:(%d == 42)", test_obj.a);
	end
endmodule
