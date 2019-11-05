/*
:name: assign_deassign
:description: assign-deassign statements test
:should_fail: 0
:tags: 10.6.1
*/
module top(clk, q, d, clr, set);

input clk, d, clr, set;
output q;
logic q;

always @(clr or set)
	if (clr)
		assign q = 0;
	else if (set)
		assign q = 1;
	else
		deassign q;

always @(posedge clk)
	q <= d;

endmodule
