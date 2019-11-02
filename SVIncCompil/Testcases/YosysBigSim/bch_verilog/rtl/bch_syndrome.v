`timescale 1ns / 1ps

/* Calculate syndromes for S_j for 1 .. 2t-1 */
module bch_syndrome #(
	parameter M = 4,
	parameter T = 3		/* Correctable errors */
) (
	input clk,
	input start,		/* Accept first syndrome bit (assumes ce) */
	input ce,		/* Accept syndrome bit */
	input data_in,
	output [2*T*M-1:M] out,
	output reg done = 0
);
	`include "bch_syndrome.vh"

	localparam TCQ = 1;

	genvar idx;
	genvar dat;

	localparam SYN_COUNT = syndrome_count(M, T);
	localparam DONE = lfsr_count(M, m2n(M)-2);
	wire [SYN_COUNT*M-1:0] syndromes;
	wire [M-1:0] count;
	reg busy = 0;

	lfsr_counter #(M) u_counter(
		.clk(clk),
		.reset(start),
		.ce(ce),
		.count(count)
	);

	always @(posedge clk) begin
		if (start) begin
			done <= #TCQ 0;
			busy <= #TCQ 1;
		end else if (ce && busy && count == DONE) begin
			done <= #TCQ 1;
			busy <= #TCQ 0;
		end else if (ce)
			done <= #TCQ 0;
	end

	/* LFSR registers */
	generate
	for (idx = 0; idx < SYN_COUNT; idx = idx + 1) begin : syndrome_gen
		if (syndrome_method(M, T, idx2syn(M, idx)) == 0)
			dsynN_method1 #(M, T, idx) u_syn(
				.clk(clk),
				.ce(ce && busy),
				.start(start),
				.data_in(data_in),
				.synN(syndromes[idx*M+:M])
			);
		else
			dsynN_method2 #(M, T, idx) u_syn(
				.clk(clk),
				.ce(ce && busy),
				.start(start),
				.data_in(data_in),
				.synN(syndromes[idx*M+:M])
			);
	end

	/* Data output */
	for (dat = 1; dat < 2 * T; dat = dat + 1) begin : assign_dat
		if (syndrome_method(M, T, dat2syn(M, dat)) == 0)
			syndrome_expand_method1 #(M) u_expand(
				.in(syndromes[dat2idx(M, dat)*M+:M]),
				.out(out[dat*M+:M])
			);
		else
			syndrome_expand_method2 #(M, dat) u_expand(
				.in(syndromes[dat2idx(M, dat)*M+:M]),
				.out(out[dat*M+:M])
			);
	end
	endgenerate

endmodule

/* Syndrome shuffling */
module bch_syndrome_shuffle #(
	parameter M = 4,
	parameter T = 3		/* Correctable errors */
) (
	input clk,
	input start,		/* Accept first syndrome bit */
	input ce,		/* Shuffle cycle */
	input [2*T*M-1:M] synN,
	output reg [(2*T-1)*M-1:0] syn_shuffled = 0
);

	`include "bch_syndrome.vh"

	localparam TCQ = 1;
	genvar i;

	/* snN drdce */
	generate
	for (i = 0; i < 2*T-1; i = i + 1) begin : s
		if (i == T + 1 && T < 4) begin
			always @(posedge clk)
				if (start)
					syn_shuffled[i*M+:M] <= #TCQ synN[(3*T-i-1)*M+:M];
		end else begin
			always @(posedge clk)
				if (start || ce)		/* xN dmul21 */
					syn_shuffled[i*M+:M] <= #TCQ start ? synN[M*((2*T+1-i)%(2*T-1)+1)+:M] : syn_shuffled[M*((i+(2*T-3))%(2*T-1))+:M];
		end
	end
	endgenerate


endmodule
