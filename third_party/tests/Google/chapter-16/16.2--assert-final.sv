/*
:name: assert_final_test
:description: assert final test
:tags: 16.4
*/
module top();

logic a = 1;

assert final (a != 0);

endmodule
