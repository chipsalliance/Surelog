/*
:name: cover_final_test
:description: cover final test
:should_fail: 0
:tags: 16.4
*/
module top();

logic a = 1;

cover final (a != 0);

endmodule
