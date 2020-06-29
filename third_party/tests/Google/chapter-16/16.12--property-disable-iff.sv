/*
:name: property_disable_iff_test
:description: property disable iff test
:tags: 16.12
*/
module top();

logic clk;
logic a;
logic b;
logic c;

assert property ( @(posedge clk) disable iff (a) b |-> c );

endmodule
