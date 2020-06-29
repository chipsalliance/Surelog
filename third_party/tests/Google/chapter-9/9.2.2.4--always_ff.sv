/*
:name: always_ff
:description: always_ff check
:tags: 9.2.2.4
*/
module always_tb ();
	wire a = 0;
	wire b = 0;
	reg q = 0;
	always_ff @(posedge a)
		q <= b;
endmodule
