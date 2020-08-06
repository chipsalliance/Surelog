/*
:name: abstract_class_inst
:description: instantiating abstract class
:should_fail_because: abstract class cannot be instantiated
:tags: 8.21
:type: simulation
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

	base_cls test_obj;

	initial begin
		test_obj = new;

		test_obj.print();
	end
endmodule
