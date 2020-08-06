/*
:name: inheritance
:description: class inheritance test
:tags: 8.13
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
		function new(int def = 42);
			super.new(def + 3);
			a = def;
		endfunction
	endclass

	test_cls test_obj;

	initial begin
		test_obj = new(37);

		$display(test_obj.incs());
		$display(test_obj.s);
	end
endmodule
