/*
:name: constructor_param
:description: class constructor with arguments test
:tags: 8.7
:type: simulation parsing
*/
module class_tb ();
	class test_cls;
		int a;
		function new(int def = 42);
			a = def;
		endfunction
	endclass

	initial begin
		test_cls test_obj = new(37);

		$display(":assert:(%d == 37)", test_obj.a);
	end
endmodule
