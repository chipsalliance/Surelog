/*
:name: always_latch_expr
:description: always_latch check
:should_fail: 0
:tags: 9.2.2.3
*/
module always_tb ();
	wire a = 0;
	wire b = 0;
	reg q = 0;
	always_latch
		if(a) q <= b;
endmodule
