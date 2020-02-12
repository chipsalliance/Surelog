/*
:name: cont_assignment_delay
:description: continuous assignment with delay test
:should_fail: 0
:tags: 10.3.3
*/
module top(input a, input b);

wire w;

assign #10 w = a & b;

endmodule
