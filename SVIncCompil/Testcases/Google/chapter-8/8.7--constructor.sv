/*
:name: constructor
:description: class constructor test
:should_fail: 0
:tags: 8.7
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

		$display(test_obj.a);
	end
endmodule
