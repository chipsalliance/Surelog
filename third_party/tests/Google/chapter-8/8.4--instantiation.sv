/*
:name: instantiation
:description: simple class instantiation test
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
