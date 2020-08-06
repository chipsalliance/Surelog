/*
:name: abstract_class
:description: class extending abstract class
:tags: 8.21
*/
module class_tb ();
	virtual class base_cls;
		pure virtual function void print();
	endclass

	class test_cls extends base_cls;
		int a = 2;
		virtual function void print();
			$display(a);
		endfunction
	endclass

	test_cls test_obj;

	initial begin
		test_obj = new;

		test_obj.print();
	end
endmodule
