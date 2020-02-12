/*
:name: assert_test
:description: assert test
:should_fail: 0
:tags: 16.2
*/
module top();

logic a = 1;

initial assert (a != 0);

endmodule
