`timescale 1ns / 1ps

module bch_decode #(
	parameter N = 15,
	parameter K = 5,
	parameter T = 3,	/* Correctable errors */
	parameter OPTION = "SERIAL"
) (
	input clk,
	input globrst,
	input start,
	input data_in,
	input ready,
	output output_valid,
	output data_out
);

`include "bch.vh"

if (T < 3) begin
	assign ready = 1;
	dec_decode #(N, K, T) u_decode(
		.clk(clk),
		.start(start),
		.data_in(data_in),
		.output_valid(output_valid),
		.data_out(data_out)
	);
end else begin
	tmec_decode #(N, K, T, OPTION) u_decode(
		.clk(clk),
		.start(start),
		.ready(ready),
		.data_in(data_in),
		.output_valid(output_valid),
		.data_out(data_out)
	);
end

endmodule
