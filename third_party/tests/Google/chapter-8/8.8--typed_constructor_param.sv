/*
:name: typed_constructor_param
:description: typed class constructor with parameters test
:tags: 8.8
*/
module class_tb ();
	class super_cls;
		int s = 2;
		function new(int def = 3);
			s = def;
		endfunction
	endclass

	class test_cls #(int t = 12) extends super_cls;
		int a;
		function new(int def = 42);
			super.new(def + 3);
			a = def - t;
		endfunction
	endclass

	super_cls super_obj;

	initial begin
	        super_obj = test_cls#(.t(23))::new(.def(41));

		$display(super_obj.s);
	end
endmodule
