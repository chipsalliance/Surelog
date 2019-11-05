/*
:name: property_disj_test
:description: property || test
:should_fail: 0
:tags: 16.12
*/
module top();

logic clk;
logic a;
logic b;

assert property ( @(posedge clk) a || b );

endmodule
