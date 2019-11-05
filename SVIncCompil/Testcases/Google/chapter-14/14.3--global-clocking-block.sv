/*
:name: global_clocking_block
:description: global clocking block test
:should_fail: 0
:tags: 14.3
*/
module top(input clk);

wire clk;

global clocking ck1 @(posedge clk); endclocking

endmodule
