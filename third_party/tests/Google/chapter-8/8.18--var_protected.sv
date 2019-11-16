/*
:name: var_protected
:description: class with protected variable
:should_fail: 0
:tags: 8.18
*/
module class_tb ();
	class a_cls;
		protected int a_prot = 2;
	endclass
endmodule
