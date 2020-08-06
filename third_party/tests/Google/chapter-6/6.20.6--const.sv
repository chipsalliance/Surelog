/*
:name: const
:description: const test
:tags: 6.20.6
*/
module top();
	class test_cls;
		int a;
		task test_method(int val);
			$display("test_method");
			a += val;
		endtask
	endclass

	const test_cls test_obj = new;
endmodule
