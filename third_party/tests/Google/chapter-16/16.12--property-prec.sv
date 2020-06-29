/*
:name: property_prec_test
:description: property with precondition test
:tags: 16.12
*/
module top();

logic clk;
logic a;
logic b;

assert property ( @(posedge clk) a |-> b);

endmodule
