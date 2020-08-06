/*
:name: parameter_unbounded
:description: unbounded parameter $ tests
:tags: 6.20.2.1
*/
module top();
	parameter p = $;
	wire clk = 0;
	wire [31:0] a;

	always @(posedge clk) a[0:p] = 23;
endmodule
