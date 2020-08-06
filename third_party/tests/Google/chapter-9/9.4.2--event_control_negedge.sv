/*
:name: event_control_negedge
:description: event control
:tags: 9.4.2
*/
module block_tb ();
	reg [3:0] a = 0;
	wire clk = 0;
	always @(negedge clk) a = ~a;
endmodule
