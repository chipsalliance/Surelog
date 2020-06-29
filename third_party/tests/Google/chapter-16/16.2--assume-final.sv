/*
:name: assume_final_test
:description: assume final test
:tags: 16.4
*/
module top(input logic a);

assume final (a != 0);

endmodule
