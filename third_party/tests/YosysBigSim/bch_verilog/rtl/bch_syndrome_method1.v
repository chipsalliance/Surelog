`timescale 1ns / 1ps

/*
 * Calculate syndrome method 1:
 *
 * S_j = r_0 + alpha^j * (r_1 + alpha^j * ...(r_(n-2) + alpha^j * r_(n-1))...)
 *
 * 0: z = n - 1, accumulator = 0
 * 1: accumulator += r_z
 * 2: accumulator *= alpha^j
 * 3: z = z - 1
 * 4: z >= 0 -> goto 1
 *
 * takes n cycles
 */
module dsynN_method1 #(
	parameter M = 4,
	parameter T = 3,
	parameter IDX = 0
) (
	input clk,
	input ce,			/* Accept additional bit */
	input start,			/* Accept first bit of syndrome */
	input data_in,
	output reg [M-1:0] synN = 0
);
	`include "bch_syndrome.vh"

	localparam TCQ = 1;
	localparam LPOW_S = lpow(M, idx2syn(M, IDX));

	wire [M-1:0] mul_out;

	/* accumulator *= alpha^j */
	parallel_standard_multiplier #(M) u_mult(
		.standard_in1(LPOW_S[M-1:0]),
		.standard_in2(synN),
		.standard_out(mul_out)
	);

	/* accumulator += r_z */
	always @(posedge clk)
		if (start)
			synN <= #TCQ {{M-1{1'b0}}, data_in};
		else if (ce)
			synN <= #TCQ mul_out ^ {{M-1{1'b0}}, data_in};
endmodule

module syndrome_expand_method1 #(
	parameter M = 4
) (
	input [M-1:0] in,
	output [M-1:0] out
);
	assign out = in;
endmodule
