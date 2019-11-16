/*
:name: cont_assignment
:description: continuous assignment test
:should_fail: 0
:tags: 10.3.2
*/
module top(input a, input b);

wire w;
assign w = a & b;

endmodule
