/*
:name: assume_test
:description: assume test
:should_fail: 0
:tags: 16.2
*/
module top(input logic a);

initial assume (a != 0);

endmodule
