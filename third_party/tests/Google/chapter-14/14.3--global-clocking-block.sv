/*
:name: global_clocking_block
:description: global clocking block test
:tags: 14.3
*/
module top(input clk);

wire clk;

global clocking ck1 @(posedge clk); endclocking

endmodule
