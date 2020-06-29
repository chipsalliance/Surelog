/*
:name: scope_resolution
:description: access static method using scope resolution operator
:tags: 8.23
*/
module class_tb ();
	class test_cls;
		static int id = 0;
		static function int next_id();
			++id;
			next_id = id;
		endfunction
	endclass

	initial begin
		$display(test_cls::next_id());
		$display(test_cls::next_id());
	end
endmodule
