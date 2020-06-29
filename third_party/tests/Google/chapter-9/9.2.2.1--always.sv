/*
:name: always
:description: always check
:tags: 9.2.2.1
*/
module always_tb ();
	wire a = 0;
	reg b = 0;
	always
		b = ~a;
endmodule
