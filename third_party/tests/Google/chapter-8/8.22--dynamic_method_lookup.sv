/*
:name: dynamic_method_lookup
:description: dynamic method selection with abstract base class
:tags: 8.22
*/
module class_tb ();
	virtual class base_cls;
		pure virtual function void print();
	endclass

	class a_cls extends base_cls;
		virtual function void print();
			$display("a");
		endfunction
	endclass

	class b_cls extends base_cls;
		virtual function void print();
			$display("b");
		endfunction
	endclass

	class c_cls extends base_cls;
		virtual function void print();
			$display("c");
		endfunction
	endclass

	base_cls arr[3];
	a_cls a;
	b_cls b;
	c_cls c;

	initial begin
		a = new;
		b = new;
		c = new;
		arr[0] = a;
		arr[1] = b;
		arr[2] = c;

		arr[0].print();
		arr[1].print();
		arr[2].print();
	end
endmodule
