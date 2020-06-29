/*
:name: event_control_posedge
:description: event control
:tags: 9.4.2
*/
module block_tb ();
	reg [3:0] a = 0;
	wire clk = 0;
	always @(posedge clk) a = ~a;
endmodule
