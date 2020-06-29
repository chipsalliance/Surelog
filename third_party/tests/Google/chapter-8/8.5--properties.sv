/*
:name: properties
:description: class properties test
:tags: 8.5
:type: simulation parsing
*/
module class_tb ();
	class test_cls;
		int a;
	endclass

	test_cls test_obj;

	initial begin
		test_obj = new;

		test_obj.a = 12;

		$display(":assert:(%d == 12)", test_obj.a);
	end
endmodule
