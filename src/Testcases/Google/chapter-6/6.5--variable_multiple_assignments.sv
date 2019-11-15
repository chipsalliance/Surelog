/*
:name: variable_multiple_assignments
:description: Variable multiple assignments tests
:should_fail: 1
:tags: 6.5
:type: simulation
*/
module top();
	int v;

	assign v = 12;
	assign v = 13;
endmodule
