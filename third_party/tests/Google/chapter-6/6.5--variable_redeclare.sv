/*
:name: variable_redeclare
:description: Variable redeclaration tests
:should_fail: 1
:tags: 6.5
:type: simulation
*/
module top();
	reg v;
	wire v;
endmodule
