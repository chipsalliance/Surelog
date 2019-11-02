/*
:name: variable_mixed_assignments
:description: Variable mixed assignments tests
:should_fail: 1
:tags: 6.5
*/
module top();
	wire clk = 0;
	int v;

	assign v = 12;
	always @(posedge clk) v <= ~v;
endmodule
