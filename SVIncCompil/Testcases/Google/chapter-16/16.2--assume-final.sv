/*
:name: assume_final_test
:description: assume final test
:should_fail: 0
:tags: 16.4
*/
module top(input a);

logic a;

assume final (a != 0);

endmodule
