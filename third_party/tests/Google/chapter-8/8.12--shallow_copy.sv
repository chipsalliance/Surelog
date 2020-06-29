/*
:name: shallow_copy
:description: object shallow copy
:tags: 8.12
*/
module class_tb ();
	class test_cls;
		int a;
		task test_method(int val);
			$display("test_method");
			a += val;
		endtask
	endclass

	test_cls test_obj0;
	test_cls test_obj1;

	initial begin
		test_obj0 = new;

		test_obj0.a = 12;

		$display(test_obj0.a);

		test_obj1 = new test_obj0;

		test_obj0.test_method(9);

		$display(test_obj1.a);
	end
endmodule
