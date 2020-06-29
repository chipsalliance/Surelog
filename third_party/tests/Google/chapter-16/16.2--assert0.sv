/*
:name: assert0_test
:description: assert #0 test
:tags: 16.4
*/
module top();

logic a = 1;

assert #0 (a != 0);

endmodule
