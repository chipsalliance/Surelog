/*
:name: variable_mixed_assignments
:description: Variable mixed assignments tests
:should_fail_because: mixed assignment types are not allowed
:tags: 6.5
:type: simulation
*/
module top();
	wire clk = 0;
	int v;

	assign v = 12;
	always @(posedge clk) v <= ~v;
endmodule
