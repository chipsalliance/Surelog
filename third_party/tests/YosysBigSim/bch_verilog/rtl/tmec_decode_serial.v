`timescale 1ns / 1ps

/*
 * serial with inversion
 * Berlekamp–Massey algorithm
 *
 * sigma_i^(r) = sigma_i^(r-1) + d_rp * beta_i^(r) (i = 1 to t-1)
 * d_r = summation sigma_i^(r) * S_(2 * r - i + 1) from i = 0 to t
 * d_rp = d_p^-1 * d_r
 *
 * combine above equations:
 * d_r = summation (simga_i^(r-1) + d_rp * beta_i^(r)) * S_(2 * r - i + 1) from i = 0 to t
 */
module tmec_decode_serial #(
	parameter M = 4,
	parameter T = 3		/* Correctable errors */
) (
	input clk,
	input syn_done,
	input bsel,
	input [log2(T)-1:0] bch_n,
	input [M-1:0] syn1,
	input [M*(2*T-1)-1:0] syn_shuffled,

	output syn_shuffle,
	output next_l,
	output ch_start,
	output reg d_r_nonzero = 0,
	output [M*(T+1)-1:0] sigma
);

	`include "bch.vh"

	localparam TCQ = 1;

	wire [M-1:0] d_r;
	wire [M-1:0] d_rp_dual;
	wire [T:0] cin;
	wire [T:0] sigma_serial;		/* 0 bits of each sigma */

	reg [M*(T+1)-1:0] beta = 0;
	reg [M*(T-1)-1:0] sigma_last = 0;	/* Last sigma values */
	reg adder_ce = 0;
	reg busy = 0;

	wire [M*4-1:0] beta0;			/* Initial beta */
	wire [M*(T+1)-1:0] d_r0;		/* Initial dr */

	wire last_cycle;
	wire first_cycle;
	wire second_cycle;
	wire penult1_cycle;
	wire penult2_cycle;

	/* beta(1)(x) = syn1 ? x^2 : x^3 */
	assign beta0 = {{{M-1{1'b0}}, !syn1}, {{M-1{1'b0}}, |syn1}, {(M*2){1'b0}}};

	/* d_r(0) = 1 + S_1 * x */
	assign d_r0 = {syn1, {(M-1){1'b0}}, 1'b1};

	always @(posedge clk) begin
		if (syn_done)
			busy <= #TCQ 1;
		else if (ch_start)
			busy <= #TCQ 0;

		if (last_cycle || syn_done)
			adder_ce <= #TCQ 1;
		else if (!busy || penult2_cycle)
			adder_ce <= #TCQ 0;

		if (syn_done) begin
			beta <= #TCQ beta0;
			sigma_last <= #TCQ beta0[2*M+:2*M];	/* beta(1) */
		end else if (last_cycle) begin
			d_r_nonzero <= #TCQ |d_r;
			sigma_last <= #TCQ sigma[0*M+:M*T];

			/* b^(r+1)(x) = x^2 * (bsel ? sigmal^(r-1)(x) : b_(r)(x)) */
			beta[2*M+:(T-1)*M] <= #TCQ (!bch_n || bsel) ? sigma_last[0*M+:(T-1)*M] : beta[0*M+:(T-1)*M];
		end
	end

	wire [M-1:0] denom;
	assign denom = syn_done ? syn1 : d_r;	/* syn1 is d_p initial value */

	/* d_rp = d_p^-1 * d_r */
	finite_divider #(M) u_dinv(
		.clk(clk),
		.start(syn_done || (first_cycle && bsel)),
		.standard_numer(d_r),
		/* d_p = S_1 ? S_1 : 1 */
		.standard_denom(denom ? denom : {1'b1}),
		.dual_out(d_rp_dual)
	);

	/* mbN SDBM d_rp * beta_i(r) */
	serial_mixed_multiplier #(M, T + 1) u_serial_mixed_multiplier(
		.clk(clk),
		.start(last_cycle),
		.dual_in(d_rp_dual),
		.standard_in(beta),
		.standard_out(cin)
	);

	/* Add Beta * drp to sigma (Summation) */
	/* simga_i^(r-1) + d_rp * beta_i^(r) */
	finite_serial_adder #(M) u_cN [T:0] (
		.clk(clk),
		.start(syn_done),
		.ce(adder_ce),
		.parallel_in(d_r0),
		.serial_in({(T+1){bch_n ? 1'b1 : 1'b0}} & cin),
		.parallel_out(sigma),
		.serial_out(sigma_serial)
	);

	/* d_r = summation (simga_i^(r-1) + d_rp * beta_i^(r)) * S_(2 * r - i + 1) from i = 0 to t */
	serial_standard_multiplier #(M, T+1) msm_serial_standard_multiplier(
		.clk(clk), 
		.run(!last_cycle),
		.start(second_cycle),
		.parallel_in(syn_shuffled[0+:M*(T+1)]),
		.serial_in(sigma_serial),
		.out(d_r)
	);

	wire [log2(M+2)-1:0] count;

	assign last_cycle = busy && count == M;
	assign first_cycle = busy && count == M+1;
	assign second_cycle = busy && count == 0;
	assign penult2_cycle = busy && count == M-2;
	assign penult1_cycle = busy && count == M-1;

	assign syn_shuffle = last_cycle;
	assign ch_start = penult1_cycle && bch_n == T-1;
	assign next_l = last_cycle;

	counter #(M+2) u_counter(
		.clk(clk),
		.reset(syn_done || first_cycle),
		.ce(busy),
		.count(count)
	);

endmodule
