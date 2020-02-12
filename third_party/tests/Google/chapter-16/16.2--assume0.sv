/*
:name: assume0_test
:description: assume #0 test
:should_fail: 0
:tags: 16.4
*/
module top(input logic a);

assume #0 (a != 0);

endmodule
