/*
:name: forward_declaration
:description: class forward declaration test
:tags: 8.27
*/
module class_tb ();
	typedef class C2;

	class C1;
		C2 c;
	endclass

	class C2;
		C1 c;
	endclass
endmodule
