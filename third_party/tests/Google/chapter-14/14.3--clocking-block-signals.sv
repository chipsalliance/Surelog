/*
:name: clocking_block_signals
:description: clocking block with signals test
:tags: 14.3
*/
module top(input clk, input a, output b, output c);

wire clk;
wire a;
wire b;
wire c;

clocking ck1 @(posedge clk);
	default input #10ns output #5ns;
	input a;
	output b;
	output #3ns c;
endclocking

always_ff @(posedge clk) begin
	b <= a;
	c <= a;
end

endmodule
