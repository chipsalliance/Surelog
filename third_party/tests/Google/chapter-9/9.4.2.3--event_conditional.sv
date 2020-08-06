/*
:name: event_conditional
:description: event conditional
:tags: 9.4.2.3
*/
module block_tb ();
	wire clk = 0;
	wire en = 0;
	wire a = 0;
	reg y;
	always @(posedge clk iff en == 1)
		y <= a;
endmodule
