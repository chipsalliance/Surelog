/*
:name: constructor_param
:description: class constructor with arguments test
:should_fail: 0
:tags: 8.7
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

		$display(test_obj.a);
	end
endmodule
