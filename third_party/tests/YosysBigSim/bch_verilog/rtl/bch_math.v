`timescale 1ns / 1ps


module matrix_vector_mult #(
	parameter C = 4,
	parameter R = C,
	parameter SHIFT = C
) (
	input [C+SHIFT*(R-1)-1:0] matrix,
	input [C-1:0] vector,
	output [R-1:0] out
);
	genvar i;
	for (i = 0; i < R; i = i + 1) begin : mult
		assign out[i] = ^(matrix[SHIFT*i+:C] & vector);
	end
endmodule


/*
 * Bit-serial Berlekamp (mixed dual/standard basis) multiplier)
 * Can multiply one dual basis input by N_INPUTS standard basis
 * inputs in M cycles, producing one bit of each output per
 * cycle
 */
module serial_mixed_multiplier #(
	parameter M = 4,
	parameter N_INPUT = 1
) (
	input clk,
	input start,
	input [M-1:0] dual_in,
	input [M*N_INPUT-1:0] standard_in,
	output [N_INPUT-1:0] standard_out
);
	`include "bch.vh"

	localparam TCQ = 1;
	localparam POLY = bch_polynomial(M);
	localparam POLY_I = polyi(M);
	localparam LPOW_P = lpow(M, POLY_I);
	localparam TO = lfsr_count(log2(M), M - POLY_I - 1);
	localparam END = lfsr_count(log2(M), M - 1);

	reg [M-1:0] lfsr = 0;
	reg [M-1:0] dual_stored = 0;
	wire [M-1:0] lfsr_in;
	wire [log2(M)-1:0] count;
	wire change;

	lfsr_counter #(log2(M)) u_counter(
		.clk(clk),
		.reset(start),
		.ce(count != END),
		.count(count)
	);
	assign change = count == TO;

	/* part of basis conversion */
	parallel_mixed_multiplier #(M) u_dmli(
		.dual_in(dual_in),
		.standard_in(LPOW_P[M-1:0]),
		.dual_out(lfsr_in)
	);

	/* LFSR for generating aux bits */
	always @(posedge clk) begin
		if (start)
			dual_stored <= #TCQ dual_in;

		if (start || change)
			lfsr <= #TCQ change ? dual_stored : lfsr_in;
		else
			lfsr <= #TCQ {^(lfsr & POLY), lfsr[M-1:1]};
	end

	matrix_vector_mult #(M, N_INPUT) u_mult(standard_in, lfsr, standard_out);
endmodule

/* Berlekamp bit-parallel dual-basis multiplier */
module parallel_mixed_multiplier #(
	parameter M = 4
) (
	input [M-1:0] dual_in,
	input [M-1:0] standard_in,
	output [M-1:0] dual_out
);
	`include "bch.vh"

	localparam POLY = bch_polynomial(M);

	wire [M-2:0] aux;
	wire [M*2-2:0] all;

	assign all = {aux, dual_in};

	/* Generate additional terms via an LFSR */
	matrix_vector_mult #(M, M-1, 1) u_lfsr(all[M*2-3:0], POLY[M-1:0], all[M*2-2:M]);

	/* Perform matrix multiplication of terms */
	matrix_vector_mult #(M, M, 1) u_mult(all, standard_in, dual_out);
endmodule

/* Bit-parallel standard basis multiplier (PPBML) */
module parallel_standard_multiplier #(
	parameter M = 4,
	parameter N_INPUT = 1
) (
	input [M-1:0] standard_in1,		/* Constant should go here */
	input [M*N_INPUT-1:0] standard_in2,
	output [M*N_INPUT-1:0] standard_out
);
	`include "bch.vh"
	genvar i, j;

	generate
	for (i = 0; i < M; i = i + 1) begin : BLOCKS
		/* alpha^i * standard_in1, each block does one mult */
		wire [M-1:0] bits;

		/* Bit i of each block */
		wire [M-1:0] z;

		/* Stage 1, multiply by alpha once for each block */
		if (i == 0)
			assign bits = standard_in1;
		else
			assign bits = mul1(M, BLOCKS[i-1].bits);

		/* Arrange bits for input into stage 2 */
		for (j = 0; j < M; j = j + 1) begin : arrange
			assign z[j] = BLOCKS[j].bits[i];
		end

		/* Perform multiplication */
		for (j = 0; j < N_INPUT; j = j + 1) begin : mult
			assign standard_out[j*M+i] = ^(standard_in2[j*M+:M] & z);
		end
	end
	endgenerate
endmodule

/*
 * Final portion of MSB first bit-serial standard basis multiplier (SPBMM)
 * Input per cycle:
 *	M{a[M-1]} & b
 *	M{a[M-2]} & b
 *	...
 *	M[a[0]} & b
 * All products of input paris are summed together.
 * Takes M cycles
 */
module serial_standard_multiplier #(
	parameter M = 4,
	parameter N_INPUT = 1
) (
	input clk,
	input run, /* FIXME: Probably not required */
	input start,
	input [M*N_INPUT-1:0] parallel_in,
	input [N_INPUT-1:0] serial_in,
	output reg [M-1:0] out = 0
);
	`include "bch.vh"

	localparam TCQ = 1;
	localparam POLY = bch_polynomial(M);

	wire [M*N_INPUT-1:0] z;
	wire [M-1:0] in;

	genvar i;
	for (i = 0; i < N_INPUT; i = i + 1) begin : mult
		assign z[i*M+:M] = {M{serial_in[i]}} & parallel_in[i*M+:M];
	end

	finite_parallel_adder #(M, N_INPUT) u_adder(z, in);

	always @(posedge clk) begin
		if (start)
			out <= #TCQ in;
		else if (run)
			out <= in ^ {out[M-2:0], 1'b0} ^ (POLY & {M{out[M-1]}});
	end
endmodule

/* Raise standard basis input to a power */
module parallel_standard_power #(
	parameter M = 4,
	parameter P = 2
) (
	input [M-1:0] standard_in,
	output [M-1:0] standard_out
);
	`include "bch.vh"

	genvar i, j;
	for (i = 0; i < M; i = i + 1) begin : out_assign
		localparam TERMS = lpow(M, i * P);
		wire [M-1:0] rot;
		for (j = 0; j < M; j = j + 1) begin : rotate
			assign rot[j] = out_assign[j].TERMS[i];
		end
		assign standard_out[i] = ^(standard_in & rot);
	end
endmodule

/*
 * Divider, takes M clock cycles.
 * Inverse of denominator is calculated by using fermat inverter:
 * 	a^(-1) = a^(2^n-2) = (a^2)*(a^2^2)*(a^2^3)....*(a^2^(m-1))
 * Wang, Charles C., et al. "VLSI architectures for computing multiplications
 * and inverses in GF (2 m)." Computers, IEEE Transactions on 100.8 (1985):
 * 709-717.
 *
 * Load denominator with start=1. If !busy (M cyles have passed), result is
 * in dual_out. Numerator is not required until busy is low.
 */
module finite_divider #(
	parameter M = 6
) (
	input clk,
	input start,
	input [M-1:0] standard_numer,
	input [M-1:0] standard_denom,
	output [M-1:0] dual_out,
	output reg busy = 0
);
	`include "bch.vh"

	localparam TCQ = 1;

	reg [M-1:0] standard_a = 0;
	wire [M-1:0] standard_b;
	reg [M-1:0] dual_c = standard_to_dual(M, lpow(M, 0));
	wire [M-1:0] dual_d;
	wire [log2(M)-1:0] count;

	assign dual_out = dual_d;

	/* Since standard_to_dual doesn't support pentanomials */
	if (bch_is_pentanomial(M))
		inverter_cannot_handle_pentanomials_yet u_ichp();

	/* Square the input each cycle */
	parallel_standard_power #(M, 2) u_dsq(
		.standard_in(start ? standard_denom : standard_a),
		.standard_out(standard_b)
	);

	/*
	 * Accumulate the term each cycle (Reuse for C = A*B^(-1) )
	 * Reuse multiplier to multiply by numerator
	 */
	parallel_mixed_multiplier #(M) u_parallel_mixed_multiplier(
		.dual_in(dual_c),
		.standard_in(busy ? standard_a : standard_numer),
		.dual_out(dual_d)
	);

	lfsr_counter #(log2(M)) u_counter(
		.clk(clk),
		.reset(start),
		.ce(1'b1),
		.count(count)
	);

	always @(posedge clk) begin
		if (start)
			busy <= #TCQ 1;
		else if (count == lfsr_count(log2(M), M - 2))
			busy <= #TCQ 0;

		if (start)
			dual_c <= #TCQ standard_to_dual(M, lpow(M, 0));
		else if (busy)
			dual_c <= #TCQ dual_d;

		if (start || busy)
			standard_a <= #TCQ standard_b;
	end
endmodule

/* out = in^3 (standard basis). Saves space vs in^2 * in */
module pow3 #(
	parameter M = 4
) (
	input [M-1:0] in,
	output [M-1:0] out
);
	`include "bch.vh"

	genvar i, j, k;
	wire [M-1:0] ft_in;
	wire [M*M-1:0] st_in;

	generate
	for (i = 0; i < M; i = i + 1) begin : FIRST_TERM
		localparam BITS = lpow(M, 3 * i);
		/* first_term = a_i * alpha^(3*i) */
		assign ft_in[i] = in[i];
	end

	/* i = 0 to m - 2, j = i to m - 1 */
	for (k = 0; k < M * M; k = k + 1) begin : SECOND_TERM
		/* i = k / M, j = j % M */
		/* second_term = a_i * a_j * (alpha^(2*i+j) + alpha^(2*i+j)) */
		localparam BITS = (k/M < k%M) ? (lpow(M, 2*(k/M)+k%M) ^ lpow(M, 2*(k%M)+k/M)) : 0;
		assign st_in[k] = (k/M < k%M) ? (in[k/M] & in[k%M]) : 0;
	end

	for (i = 0; i < M; i = i + 1) begin : CALC
		wire [M-1:0] first_term;
		wire [M*M-1:0] second_term;

		/* Rearrange bits for multiplication */
		for (j = 0; j < M; j = j + 1) begin : arrange1
			assign first_term[j] = FIRST_TERM[j].BITS[i];
		end

		for (j = 0; j < M*M; j = j + 1) begin : arrange2
			assign second_term[j] = SECOND_TERM[j].BITS[i];
		end

		/* a^3 = first_term + second_term*/
		assign out[i] = ^(ft_in & first_term) ^ ^(st_in & second_term);
	end
	endgenerate
endmodule

/* Finite adder, xor each bit */
module finite_parallel_adder #(
	parameter M = 4,
	parameter N_INPUT = 2
) (
	input [M*N_INPUT-1:0] in,
	output [M-1:0] out
);
	genvar i, j;

	for (i = 0; i < M; i = i + 1) begin : add
		wire [N_INPUT-1:0] z;
		for (j = 0; j < N_INPUT; j = j + 1) begin : arrange
			assign z[j] = in[j*M+i];
		end
		assign out[i] = ^z;
	end
endmodule

module finite_serial_adder #(
	parameter M = 4
) (
	input clk,
	input start,
	input ce,
	input [M-1:0] parallel_in,
	input serial_in,
	output reg [M-1:0] parallel_out = 0,
	output serial_out
);
	localparam TCQ = 1;

	always @(posedge clk)
		if (start)
			parallel_out <= #TCQ {parallel_in[0+:M-1], parallel_in[M-1]};
		else if (ce)
			parallel_out <= #TCQ {parallel_out[0+:M-1], parallel_out[M-1] ^ serial_in};
	assign serial_out = parallel_out[0];
endmodule

module lfsr_counter #(
	parameter M = 4
) (
	input clk,
	input reset,
	input ce,
	output reg [M-1:0] count = 1
);
	`include "bch.vh"

	localparam TCQ = 1;
	localparam POLY = bch_polynomial(M);

	always @(posedge clk)
		if (reset)
			count <= #TCQ 1'b1;
		else if (ce)
			count <= #TCQ {count[M-2:0], 1'b0} ^ ({M{count[M-1]}} & POLY);
endmodule

module counter #(
	parameter MAX = 15
) (
	input clk,
	input reset,
	input ce,
	output reg [log2(MAX)-1:0] count = 0
);
	`include "bch.vh"

	localparam TCQ = 1;

	always @(posedge clk)
		if (reset)
			count <= #TCQ 1'b0;
		else if (ce)
			count <= #TCQ count + 1'b1;
endmodule

