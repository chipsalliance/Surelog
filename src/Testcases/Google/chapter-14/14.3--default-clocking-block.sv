/*
:name: default_clocking_block
:description: default clocking block test
:should_fail: 0
:tags: 14.3
*/
module top(input clk);

wire clk;

default clocking @(posedge clk);
	default input #10ns output #5ns;
endclocking

endmodule
