/*
:name: properties_enum
:description: enum defined inside class
:tags: 8.5
*/
module class_tb ();
	class test_cls;
		typedef enum {A = 10, B = 20, C = 30, D = 1} e_type;
	endclass

	test_cls test_obj;

	initial begin
		test_obj = new;
		$display(test_obj.C);
	end
endmodule
