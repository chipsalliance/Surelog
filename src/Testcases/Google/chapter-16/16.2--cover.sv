/*
:name: cover_test
:description: cover test
:should_fail: 0
:tags: 16.2
*/
module top();

logic a = 1;

cover (a != 0);

endmodule
