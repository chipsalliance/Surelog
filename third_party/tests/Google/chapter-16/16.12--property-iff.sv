/*
:name: property_iff_test
:description: property iff test
:tags: 16.12
*/
module top();

logic clk;
logic a;
logic b;

assert property ( @(posedge clk) a iff b );

endmodule
