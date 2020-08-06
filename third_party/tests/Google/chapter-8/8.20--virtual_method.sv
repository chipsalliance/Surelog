/*
:name: virtual_method
:description: class with virtual methods
:tags: 8.20
*/
module class_tb ();
	class super_cls;
		int a = 1;
		virtual function void print();
			$display("super_cls::a: %d", a);
		endfunction
	endclass

	class test_cls extends super_cls;
		int a = 2;
		virtual function void print();
			$display("test_cls::a: %d", a);
		endfunction
	endclass

	test_cls test_obj;
	super_cls super_obj;

	initial begin
		test_obj = new;
		super_obj = new;

		test_obj.print();
		super_obj.print();

		super_obj = test_obj;

		test_obj.print();
		super_obj.print();
	end
endmodule
