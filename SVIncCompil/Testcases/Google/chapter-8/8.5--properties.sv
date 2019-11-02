/*
:name: properties
:description: class properties test
:should_fail: 0
:tags: 8.5
*/
module class_tb ();
	class test_cls;
		int a;
	endclass

	test_cls test_obj;

	initial begin
		test_obj = new;

		test_obj.a = 12;

		$display(test_obj.a);
	end
endmodule
