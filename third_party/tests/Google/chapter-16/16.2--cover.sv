/*
:name: cover_test
:description: cover test
:tags: 16.2
*/
module top();

logic a = 1;

initial cover (a != 0);

endmodule
