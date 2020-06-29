/*
:name: override_member
:description: class member override test
:tags: 8.14
*/
module class_tb ();
	class super_cls;
		int s = 2;
		function int incs();
			++s;
			incs = s;
		endfunction
		function new(int def = 3);
			s = def;
		endfunction
	endclass

	class test_cls extends super_cls;
		int a;
		function int incs();
			s += 2;
			incs = s;
		endfunction
		function new(int def = 42);
			super.new(def + 3);
			a = def;
		endfunction
	endclass

	test_cls test_obj;
	super_cls super_obj;

	initial begin
		test_obj = new(37);
		super_obj = test_obj;

		$display(test_obj.s);
		$display(test_obj.incs());
		$display(test_obj.s);
		$display(super_obj.incs());
	end
endmodule
