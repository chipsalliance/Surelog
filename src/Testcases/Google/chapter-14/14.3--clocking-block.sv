/*
:name: clocking_block
:description: clocking block test
:should_fail: 0
:tags: 14.3
*/
module top(input clk);

wire clk;

clocking ck1 @(posedge clk);
	default input #10ns output #5ns;
endclocking

endmodule
