/*
:name: instantiation
:description: simple class instantiation test
:should_fail: 0
:tags: 8.4
*/
module class_tb ();
	class test_cls;
		int a;
	endclass

	test_cls test_obj;

	initial begin
		if(test_obj == null) test_obj = new;
	end
endmodule
