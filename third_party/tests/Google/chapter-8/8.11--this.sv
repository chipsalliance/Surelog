/*
:name: this
:description: this keyword test
:tags: 8.11
*/
module class_tb ();
	class test_cls;
		int a;
		task test_method(int a);
			$display("test_method");
			this.a += a;
		endtask
	endclass
endmodule
