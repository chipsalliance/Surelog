/*
:name: parameter_aggregate
:description: parameter aggregate type tests
:should_fail: 0
:tags: 6.20.2
*/
module top();
	parameter logic [31:0] p [3:0] = '{1, 2, 3, 4};
endmodule
