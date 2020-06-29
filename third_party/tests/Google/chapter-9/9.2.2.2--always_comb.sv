/*
:name: always_comb
:description: always_comb check
:tags: 9.2.2.2
*/
module always_tb ();
	wire a = 0;
	reg b = 0;
	always_comb
		b = ~a;
endmodule
