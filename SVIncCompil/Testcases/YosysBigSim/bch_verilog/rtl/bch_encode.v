`timescale 1ns / 1ps

module bch_encode #(
	parameter N = 15,	/* Code + Input (Output) */
	parameter K = 5,	/* Input size */
	parameter T = 3		/* Correctable errors */
) (
	input clk,
	input globrst,
	input start,		/* First cycle */
	input data_in,		/* Input data */
	output reg data_out = 0,/* Encoded output */
	output reg first = 0,	/* First output cycle */
	output reg last = 0,	/* Last output cycle */
	output reg penult = 0,	/* Next cycle is last output cycle */
	output reg busy = 0
);

`include "bch.vh"

/* Calculate least common multiple which has x^2t .. x as its roots */
function [N-K-1:0] encoder_poly;
	input dummy;
	integer nk;
	integer i;
	integer j;
	integer a;
	integer curr;
	integer prev;
	reg [(N-K+1)*M-1:0] poly;
	reg [N-1:0] roots;
begin

	/* Calculate the roots for this finite field */
	roots = 0;
	for (i = 0; i < T; i = i + 1) begin
		a = 2 * i + 1;
		for (j = 0; j < M; j = j + 1) begin
			roots[a] = 1;
			a = (2 * a) % N;
		end
	end

	nk = 0;
	poly = 1;
	a = lpow(M, 0);
	for (i = 0; i < N; i = i + 1) begin
		if (roots[i]) begin
			prev = 0;
			poly[(nk+1)*M+:M] = 1;
			for (j = 0; j <= nk; j = j + 1) begin
				curr = poly[j*M+:M];
				poly[j*M+:M] = finite_mult(M, curr, a) ^ prev;
				prev = curr;
			end
			nk = nk + 1;
		end
		a = mul1(M, a);
	end

	for (i = 0; i < nk; i = i + 1)
		encoder_poly[i] = poly[i*M+:M] ? 1 : 0;
end
endfunction

localparam TCQ = 1;
localparam M = n2m(N);
localparam ENC = encoder_poly(0);
reg [N-K-1:0] lfsr = 0;
wire [M-1:0] count;
reg load_lfsr = 0;

/* Input XOR with highest LFSR bit */
wire lfsr_in = load_lfsr && (lfsr[N-K-1] ^ data_in);

lfsr_counter #(M) u_counter(
	.clk(clk),
	.reset(start),
	.ce(1'b1),
	.count(count)
);

always @(posedge clk) begin
	first <= #TCQ start;
	penult <= #TCQ !start && busy && count == lfsr_count(M, N - 3);
	last <= !start && penult;

	/*
	 * Keep track of whether or not we are running so we don't send out
	 * spurious last signals as the count wraps around.
	 */
	if (start)
		busy <= #TCQ 1;
	else if (last)
		busy <= #TCQ 0;

	/* c1 ecount */
	if (start)
		load_lfsr <= #TCQ 1'b1;
	else if (count == lfsr_count(M, K - 2))
		load_lfsr <= #TCQ 1'b0;

	/* r1 ering */
	if (start)
		lfsr <= #TCQ {N-K{data_in}} & ENC;
	else
		lfsr <= #TCQ {lfsr[N-K-2:0], 1'b0} ^ ({N-K{lfsr_in}} & ENC);

	data_out <= #TCQ (load_lfsr || start) ? data_in : lfsr[N-K-1];
end

endmodule
