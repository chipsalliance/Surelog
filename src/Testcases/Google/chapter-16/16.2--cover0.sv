/*
:name: cover0_test
:description: cover #0 test
:should_fail: 0
:tags: 16.4
*/
module top();

logic a = 1;

cover #0 (a != 0);

endmodule
