/*
:name: variable_multiple_assignments
:description: Variable multiple assignments tests
:should_fail_because: multiple continuous assignements are not allowed
:tags: 6.5
:type: simulation
*/
module top();
	int v;

	assign v = 12;
	assign v = 13;
endmodule
