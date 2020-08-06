/*
:name: specparam_inv
:description: specparam assignment to param should be invalid
:should_fail_because: specparam assignment to param should be invalid
:tags: 6.20.5
:type: simulation
*/
module top();
	specparam delay = 50;
	parameter p = delay + 2;
endmodule
