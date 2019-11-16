/*
:name: assert_final_test
:description: assert final test
:should_fail: 0
:tags: 16.4
*/
module top();

logic a = 1;

assert final (a != 0);

endmodule
