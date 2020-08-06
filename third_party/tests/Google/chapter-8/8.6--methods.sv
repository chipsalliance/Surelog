/*
:name: methods
:description: class method test
:tags: 8.6
*/
module class_tb ();
	class test_cls;
		int a;
		task test_method(int val);
			$display("test_method");
			a += val;
		endtask
	endclass

	test_cls test_obj;

	initial begin
		test_obj = new;

		test_obj.a = 12;

		$display(test_obj.a);

		test_obj.test_method(9);

		$display(test_obj.a);
	end
endmodule
