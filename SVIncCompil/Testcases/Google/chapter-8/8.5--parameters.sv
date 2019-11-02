/*
:name: parameters
:description: parametrized class test
:should_fail: 0
:tags: 8.5 8.25
*/
module class_tb ();
	class test_cls #(parameter a = 12);
	endclass

	test_cls #(34) test_obj;

	initial begin
		test_obj = new;
		$display(test_cls.a);
	end
endmodule
