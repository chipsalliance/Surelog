`timescale 1ns / 1ps

/* Chien search, determines roots of a polynomial defined over a finite field */

module dch #(
	parameter M = 4,
	parameter P = 1
) (
	input clk,
	input err,		/* Error was found so correct it */
	input ce,
	input start,
	input [M-1:0] in,
	output reg [M-1:0] out = 0
);
	`include "bch.vh"

	localparam TCQ = 1;
	localparam LPOW = lpow(M, P);

	wire [M-1:0] mul_out;

	parallel_standard_multiplier #(M) u_mult(
		.standard_in1(LPOW[M-1:0]),
		.standard_in2(out ^ err),
		.standard_out(mul_out)
	);

	always @(posedge clk)
		if (start)
			/* Initialize with coefficients of the error location polynomial */
			out <= #TCQ in;
		else if (ce)
			/* Multiply by alpha^P */
			out <= #TCQ mul_out;
endmodule

/*
 * Tradition chien search, for each cycle, check if the
 * sum of all the equations is zero, if so, this location
 * is a bit error. K cycles are required.
 *
 * Each register is loaded with the associated syndrome
 * and multiplied by alpha^i each cycle.
 */
module chien #(
	parameter M = 4,
	parameter K = 5,
	parameter T = 3
) (
	input clk,
	input ce,
	input start,
	input [M*(T+1)-1:0] sigma,
	output done,
	output err
);
	`include "bch.vh"

	wire [M-1:0] eq;
	wire [M*(T+1)-1:0] z;
	wire [M*(T+1)-1:0] chien_mask;
	wire [M-1:0] count;
	reg busy = 0;
	
	localparam TCQ = 1;

	genvar i;
	generate
	/* Chien search */
	for (i = 0; i <= T; i = i + 1) begin : ch
		dch #(M, i) u_ch(
			.clk(clk),
			.err(1'b0),
			.ce(ce && busy),
			.start(start),
			.in(sigma[i*M+:M]),
			.out(z[i*M+:M])
		);
	end
	endgenerate

	lfsr_counter #(M) u_counter(
		.clk(clk),
		.reset(start),
		.ce(busy),
		.count(count)
	);
	assign done = busy && (count == lfsr_count(M, K));
	always @(posedge clk)
		busy <= #TCQ start || (busy && !done);

	finite_parallel_adder #(M, T+1) u_dcheq(z, eq);

	assign err = !eq;
endmodule
