/*
:name: property_test
:description: property test
:tags: 16.12
*/
module top();

logic clk;
logic a;

assert property ( @(posedge clk) (a == 1));

endmodule
