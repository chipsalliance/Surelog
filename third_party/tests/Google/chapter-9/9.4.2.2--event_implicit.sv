/*
:name: event_implicit
:description: event implicit list
:should_fail: 0
:tags: 9.4.2.2
*/
module block_tb ();
	wire a = 0;
	wire b = 0;
	wire c = 0;
	wire d = 0;
	wire out = 0;
	always @(*)
		out = (a | b) & (c | d);
endmodule
