/*
:name: disable
:description: disable block
:tags: 9.6.2
*/
module fork_tb ();
	reg a = 0;
	reg b = 0;
	initial begin: block
		a = 1;
		disable block;
		b = 1;
	end
endmodule
