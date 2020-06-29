/*
:name: cont_assignment_net_delay
:description: continuous assignment with net delay test
:tags: 10.3.3
*/
module top(input a, input b);

wire #10 w;

assign w = a & b;

endmodule
