`timescale 1ns / 1ps

/* parallel inversionless */
module tmec_decode_parallel #(
	parameter M = 4,
	parameter T = 3		/* Correctable errors */
) (
	input clk,
	input syn_done,
	input bsel,
	input [log2(T+1)-1:0] bch_n,
	input [M-1:0] syn1,
	input [M*(2*T-1)-1:0] syn_shuffled,

	output next_l,
	output reg syn_shuffle = 0,
	output reg ch_start = 0,
	output d_r_nonzero,
	output reg [M*(T+1)-1:0] sigma = 0
);
	`include "bch.vh"

	localparam TCQ = 1;

	reg [M-1:0] d_r = 0;
	wire [M-1:0] d_r_next;
	reg [M-1:0] d_p = 0;
	wire [M*(T+1)-1:0] d_r_terms;
	wire [M*(T+1)-1:0] d_p_sigma;
	wire [M*(T+1)-1:0] d_r_beta;
	reg [M*(T+1)-1:0] beta = 0;
	reg busy = 0;

	assign next_l = !syn_shuffle;

	genvar i;

	/* beta(1)(x) = syn1 ? x^2 : x^3 */
	wire [M*4-1:0] beta0;
	assign beta0 = {{M-1{1'b0}}, !syn1, {M-1{1'b0}}, |syn1, {2*M{1'b0}}};

	/* d_r(0) = 1 + S_1 * x */
	wire [M*2-1:0] sigma0;
	assign sigma0 = {syn1, {M-1{1'b0}}, 1'b1};

	assign d_r_nonzero = |d_r;

	always @(posedge clk) begin
		if (syn_done) begin
			busy <= #TCQ 1;
			syn_shuffle <= #TCQ 0;
		end else if (busy && !ch_start)
			syn_shuffle <= #TCQ ~syn_shuffle;
		else begin
			busy <= #TCQ 0;
			syn_shuffle <= #TCQ 0;
		end

		ch_start <= #TCQ busy && syn_shuffle && bch_n == T-1;
			
		if (syn_done) begin
			d_p <= #TCQ syn1 ? syn1 : 1;
			sigma <= #TCQ sigma0;
			beta <= #TCQ beta0;
		end else if (busy && !syn_shuffle)
			d_r <= #TCQ d_r_next;
		else if (busy) begin
			/* d_p = bsel ? d_r : d_p */
			if (bsel)
				d_p <= #TCQ d_r;

			/* sigma^(r)(x) = d_p * sigma^(r-1)(x) - d_r * beta^(r)(x) */
			sigma <= #TCQ {d_p_sigma ^ d_r_beta};

			/* b^(r+1)(x) = x^2 * (bsel ? sigmal^(r-1)(x) : b_(r)(x)) */
			beta[2*M+:M*(T-1)] <= #TCQ bsel ? sigma[0*M+:M*(T-1)] : beta[0*M+:M*(T-1)];
		end
	end

	/* d_r * beta^(r)(x) */
	parallel_standard_multiplier #(M, T+1) u_mbn(
		.standard_in1(d_r),
		.standard_in2(beta),
		.standard_out(d_r_beta)
	);

	for (i = 0; i <= T; i = i + 1) begin : parallel_standard_multiplier
		/* d_r_terms = {sigma_i^(r) * S_(2 * r - i + 1)}[0..t], d_p * sigma^(r-1)(x) */
		parallel_standard_multiplier #(M, 2) u_mn(
			.standard_in1(sigma[i*M+:M]),
			.standard_in2({syn_shuffled[i*M+:M], d_p}),
			.standard_out({d_r_terms[i*M+:M], d_p_sigma[i*M+:M]})
		);
	end

	/* d_r = summation of dr_terms */
	finite_parallel_adder #(M, T+1) u_generate_cs(d_r_terms, d_r_next);

endmodule
