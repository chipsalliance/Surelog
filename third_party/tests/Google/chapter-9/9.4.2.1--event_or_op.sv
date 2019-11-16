/*
:name: event_or_op
:description: event or operator
:should_fail: 0
:tags: 9.4.2.1
*/
module block_tb ();
	wire a = 0;
	wire b = 0;
	wire c = 0;
	wire d = 0;
	wire out = 0;
	always @(a or b or c or d)
		out = (a | b) & (c | d);
endmodule
