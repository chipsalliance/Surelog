`timescale 1ns / 1ps

module tmec_decode #(
	parameter N = 15,
	parameter K = 5,
	parameter T = 3,	/* Correctable errors */
	parameter OPTION = "SERIAL"
) (
	input clk,
	input start,
	input data_in,
	output reg ready = 1,
	output reg output_valid = 0,
	output reg data_out = 0
);

`include "bch.vh"

localparam TCQ = 1;
localparam M = n2m(N);
localparam BUF_SIZE = OPTION == "SERIAL" ? (N + T * (M + 2) + 0) : (N + T*2 + 1);

if (BUF_SIZE > 2 * N) begin
	wire [log2(BUF_SIZE - N + 3)-1:0] wait_count;
	counter #(BUF_SIZE - N + 2) u_wait(
		.clk(clk),
		.reset(start),
		.ce(!ready),
		.count(wait_count)
	);
	always @(posedge clk) begin
		if (start)
			ready <= #TCQ 0;
		else if (wait_count == BUF_SIZE - N + 2)
			ready <= #TCQ 1;
	end
end

reg [BUF_SIZE-1:0] buf_ = 0;
wire [M*(2*T-1)-1:0] syn_shuffled;
wire [2*T*M-1:M] synN;
wire [M*(T+1)-1:0] sigma;

wire bsel;
wire ch_start;
wire next_l;
wire d_r_nonzero;
wire err;
wire syn_done;

wire syn_shuffle;
reg next_output_valid = 0;
wire ch_done;
reg ch_ready = 0;
wire [log2(T)-1:0] bch_n;

if (OPTION == "PARALLEL") begin
	tmec_decode_parallel #(M, T) u_decode_parallel (
		.clk(clk),
		.syn_done(syn_done),
		.bsel(bsel),
		.bch_n(bch_n),
		.syn1(synN[1*M+:M]),
		.syn_shuffled(syn_shuffled),
		.syn_shuffle(syn_shuffle),
		.next_l(next_l),
		.ch_start(ch_start),
		.d_r_nonzero(d_r_nonzero),
		.sigma(sigma)
	);
end else if (OPTION == "SERIAL") begin
	tmec_decode_serial #(M, T) u_decode_serial (
		.clk(clk),
		.syn_done(syn_done),
		.bsel(bsel),
		.bch_n(bch_n),
		.syn1(synN[1*M+:M]),
		.syn_shuffled(syn_shuffled),
		.syn_shuffle(syn_shuffle),
		.next_l(next_l),
		.ch_start(ch_start),
		.d_r_nonzero(d_r_nonzero),
		.sigma(sigma)
	);
end else
	illegal_option_value u_iov();

reg [log2(T+1)-1:0] l = 0;
wire syn1_nonzero = |synN[1*M+:M];

counter #(T) u_bch_n_counter(
	.clk(clk),
	.reset(syn_done),
	.ce(next_l),
	.count(bch_n)
);

assign bsel = d_r_nonzero && bch_n >= l;

always @(posedge clk)
	if (syn_done)
		l <= #TCQ {{log2(T+1)-1{1'b0}}, syn1_nonzero};
	else if (next_l)
		if (bsel)
			l <= #TCQ 2 * bch_n - l + 1;

bch_syndrome #(M, T) u_bch_syndrome(
	.clk(clk),
	.ce(1'b1),
	.start(start),
	.done(syn_done),
	.data_in(data_in),
	.out(synN)
);

bch_syndrome_shuffle #(M, T) u_bch_syndrome_shuffle(
	.clk(clk),
	.start(syn_done),
	.ce(syn_shuffle),
	.synN(synN),
	.syn_shuffled(syn_shuffled)
);

chien #(M, K, T) u_chien(
	.clk(clk),
	.ce(1'b1),
	.start(ch_start),
	.sigma(sigma),
	.done(ch_done),
	.err(err)
);

always @(posedge clk) begin
	if (ch_ready)
		next_output_valid <= #TCQ 1;
	else if (ch_done)
		next_output_valid <= #TCQ 0;
	output_valid <= #TCQ next_output_valid;
	ch_ready <= #TCQ ch_start;

	buf_ <= #TCQ {buf_[BUF_SIZE-2:0], data_in};
	data_out <= #TCQ (buf_[BUF_SIZE-1] ^ err) && next_output_valid;
end

endmodule
