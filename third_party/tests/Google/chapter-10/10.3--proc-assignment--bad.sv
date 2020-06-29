/*
:name: proc_assignment__bad
:description: continuous assignment with delay test
:should_fail_because: it's illegal to procedurally assign to wire, IEEE Table 10-1
:tags: 10.3
:type: simulation
*/
module top(input a, input b);

wire w;

initial
	w = #10 a & b;

endmodule
