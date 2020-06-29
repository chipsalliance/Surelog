/*
:name: typed_constructor
:description: class typed constructor test
:tags: 8.8
*/
module class_tb ();
	class super_cls;
		int s = 2;
		function new(int def = 3);
			s = def;
		endfunction
	endclass

	class test_cls extends super_cls;
		int a;
		function new(int def = 42);
			super.new(def + 3);
			a = def;
		endfunction
	endclass

	test_cls super_obj;

	initial begin
		super_obj = test_cls::new;

		$display(super_obj.s);
	end
endmodule
