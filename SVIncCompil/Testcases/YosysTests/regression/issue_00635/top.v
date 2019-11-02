module top
(
	input clk,
	input rstn,
	input en,
	input [XLEN-1:0] d,
	output [XLEN-1:0] q
);
parameter XLEN = 4;
