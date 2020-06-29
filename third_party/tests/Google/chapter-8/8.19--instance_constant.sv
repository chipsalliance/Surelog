/*
:name: instance_constant
:description: class with instance constant variable
:tags: 8.19
*/
module class_tb ();
	class a_cls;
		const int c;
		function new(int val);
			c = 20 * val;
		endfunction
	endclass
endmodule
