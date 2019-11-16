/*
:name: assume0_test
:description: assume #0 test
:should_fail: 0
:tags: 16.4
*/
module top(input a);

logic a;

assume #0 (a != 0);

endmodule
