/*
 *  Copyright (C) 2017  Clifford Wolf <clifford@clifford.at>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

module smartbextdep (
	input clock,
	input bdep,
	input [31:0] rs1,
	input [31:0] rs2,
	output reg [31:0] rd
);
	wire        din_mode;
	wire [31:0] din_value;
	wire [31:0] din_mask;
	wire [31:0] dout_result;

	assign din_mode  = bdep;
	assign din_value = rs1;
	assign din_mask  = rs2;

	smartbextdep_direct smartbextdep_direct_inst (
		.din_mode   (din_mode   ),
		.din_value  (din_value  ),
		.din_mask   (din_mask   ),
		.dout_result(dout_result)
	);

	always @(posedge clock) begin
		rd <= dout_result;
	end
endmodule

// ========================================================================

`define smartbextdep_bfly_idx_a(k, i) ((2 << (k))*((i)/(1 << (k))) + (i)%(1 << (k)))
`define smartbextdep_bfly_idx_b(k, i) (`smartbextdep_bfly_idx_a(k, i) + (1<<(k)))

module smartbextdep_direct (
	input         din_mode,
	input  [31:0] din_value,
	input  [31:0] din_mask,
	output [31:0] dout_result
);
	wire [15:0] decoder_s1, decoder_s2, decoder_s4;
	wire [15:0] decoder_s8, decoder_s16, decoder_s32;

	smartbextdep_decoder decoder (
		.mask  (din_mask   ),
		.s1    (decoder_s1 ),
		.s2    (decoder_s2 ),
		.s4    (decoder_s4 ),
		.s8    (decoder_s8 ),
		.s16   (decoder_s16)
	);

	wire [31:0] result_fwd;
	wire [31:0] result_bwd;

	smartbextdep_bfly_fwd butterfly_fwd (
		.din  (din_value   ),
		.s1   (~decoder_s1 ),
		.s2   (~decoder_s2 ),
		.s4   (~decoder_s4 ),
		.s8   (~decoder_s8 ),
		.s16  (~decoder_s16),
		.dout (result_fwd  )
	);

	smartbextdep_bfly_bwd butterfly_bwd (
		.din  (din_value & din_mask),
		.s1   (~decoder_s1 ),
		.s2   (~decoder_s2 ),
		.s4   (~decoder_s4 ),
		.s8   (~decoder_s8 ),
		.s16  (~decoder_s16),
		.dout (result_bwd  )
	);

	assign dout_result = din_mode ? (result_fwd & din_mask) : result_bwd;
endmodule

// ========================================================================

module smartbextdep_lrotcz #(
	parameter integer N = 1,
	parameter integer M = 1
) (
	input [7:0] din,
	output [M-1:0] dout
);
	wire [2*M-1:0] mask = {M{1'b1}};
	assign dout = (mask << din[N-1:0]) >> M;
endmodule

module smartbextdep_decoder (
	input         clock,
	input         enable,
	input  [31:0] mask,
	output [15:0] s1, s2, s4, s8, s16
);
	wire [8*32-1:0] ppsdata;

	smartbextdep_pps32 pps_core (
		.din  (mask),
		.dout (ppsdata)
	);

	genvar i;
	generate
		for (i = 0; i < 32/2; i = i+1) begin:stage1
			smartbextdep_lrotcz #(.N(1), .M(1)) lrotc_zero (
				.din(ppsdata[8*(2*i + 1 - 1) +: 8]),
				.dout(s1[i])
			);
		end

		for (i = 0; i < 32/4; i = i+1) begin:stage2
			smartbextdep_lrotcz #(.N(2), .M(2)) lrotc_zero (
				.din(ppsdata[8*(4*i + 2 - 1) +: 8]),
				.dout(s2[2*i +: 2])
			);
		end

		for (i = 0; i < 32/8; i = i+1) begin:stage4
			smartbextdep_lrotcz #(.N(3), .M(4)) lrotc_zero (
				.din(ppsdata[8*(8*i + 4 - 1) +: 8]),
				.dout(s4[4*i +: 4])
			);
		end

		for (i = 0; i < 32/16; i = i+1) begin:stage8
			smartbextdep_lrotcz #(.N(4), .M(8)) lrotc_zero (
				.din(ppsdata[8*(16*i + 8 - 1) +: 8]),
				.dout(s8[8*i +: 8])
			);
		end

		for (i = 0; i < 32/32; i = i+1) begin:stage16
			smartbextdep_lrotcz #(.N(5), .M(16)) lrotc_zero (
				.din(ppsdata[8*(32*i + 16 - 1) +: 8]),
				.dout(s16[16*i +: 16])
			);
		end
	endgenerate
endmodule

module smartbextdep_bfly_fwd (
	input  [31:0] din,
	input  [15:0] s1, s2, s4, s8, s16,
	output [31:0] dout
);
	reg [31:0] butterfly;
	assign dout = butterfly;

	integer k, i;
	always @* begin
		butterfly = din;

		for (i = 0; i < 16; i = i+1)
			if (s16[i]) {butterfly[`smartbextdep_bfly_idx_a(4, i)], butterfly[`smartbextdep_bfly_idx_b(4, i)]} =
						{butterfly[`smartbextdep_bfly_idx_b(4, i)], butterfly[`smartbextdep_bfly_idx_a(4, i)]};

		for (i = 0; i < 16; i = i+1)
			if (s8[i]) {butterfly[`smartbextdep_bfly_idx_a(3, i)], butterfly[`smartbextdep_bfly_idx_b(3, i)]} =
						{butterfly[`smartbextdep_bfly_idx_b(3, i)], butterfly[`smartbextdep_bfly_idx_a(3, i)]};

		for (i = 0; i < 16; i = i+1)
			if (s4[i]) {butterfly[`smartbextdep_bfly_idx_a(2, i)], butterfly[`smartbextdep_bfly_idx_b(2, i)]} =
						{butterfly[`smartbextdep_bfly_idx_b(2, i)], butterfly[`smartbextdep_bfly_idx_a(2, i)]};

		for (i = 0; i < 16; i = i+1)
			if (s2[i]) {butterfly[`smartbextdep_bfly_idx_a(1, i)], butterfly[`smartbextdep_bfly_idx_b(1, i)]} =
						{butterfly[`smartbextdep_bfly_idx_b(1, i)], butterfly[`smartbextdep_bfly_idx_a(1, i)]};

		for (i = 0; i < 16; i = i+1)
			if (s1[i]) {butterfly[`smartbextdep_bfly_idx_a(0, i)], butterfly[`smartbextdep_bfly_idx_b(0, i)]} =
						{butterfly[`smartbextdep_bfly_idx_b(0, i)], butterfly[`smartbextdep_bfly_idx_a(0, i)]};
	end
endmodule

module smartbextdep_bfly_bwd (
	input  [31:0] din,
	input  [15:0] s1, s2, s4, s8, s16,
	output [31:0] dout
);
	reg [31:0] butterfly;
	assign dout = butterfly;

	integer k, i;
	always @* begin
		butterfly = din;

		for (i = 0; i < 16; i = i+1)
			if (s1[i]) {butterfly[`smartbextdep_bfly_idx_a(0, i)], butterfly[`smartbextdep_bfly_idx_b(0, i)]} =
						{butterfly[`smartbextdep_bfly_idx_b(0, i)], butterfly[`smartbextdep_bfly_idx_a(0, i)]};

		for (i = 0; i < 16; i = i+1)
			if (s2[i]) {butterfly[`smartbextdep_bfly_idx_a(1, i)], butterfly[`smartbextdep_bfly_idx_b(1, i)]} =
						{butterfly[`smartbextdep_bfly_idx_b(1, i)], butterfly[`smartbextdep_bfly_idx_a(1, i)]};

		for (i = 0; i < 16; i = i+1)
			if (s4[i]) {butterfly[`smartbextdep_bfly_idx_a(2, i)], butterfly[`smartbextdep_bfly_idx_b(2, i)]} =
						{butterfly[`smartbextdep_bfly_idx_b(2, i)], butterfly[`smartbextdep_bfly_idx_a(2, i)]};

		for (i = 0; i < 16; i = i+1)
			if (s8[i]) {butterfly[`smartbextdep_bfly_idx_a(3, i)], butterfly[`smartbextdep_bfly_idx_b(3, i)]} =
						{butterfly[`smartbextdep_bfly_idx_b(3, i)], butterfly[`smartbextdep_bfly_idx_a(3, i)]};

		for (i = 0; i < 16; i = i+1)
			if (s16[i]) {butterfly[`smartbextdep_bfly_idx_a(4, i)], butterfly[`smartbextdep_bfly_idx_b(4, i)]} =
						{butterfly[`smartbextdep_bfly_idx_b(4, i)], butterfly[`smartbextdep_bfly_idx_a(4, i)]};
	end
endmodule

module smartbextdep_pps32 (
  input [31:0] din,
  output [255:0] dout
);
  function [15:0] carry_save_add;
    input [15:0] a, b;
    reg [7:0] x, y;
    begin
      x = a[15:8] ^ a[7:0] ^ b[7:0];
      y = ((a[15:8] & a[7:0]) | (a[15:8] & b[7:0]) | (a[7:0] & b[7:0])) << 1;
      carry_save_add[7:0] = x ^ y ^ b[15:8];
      carry_save_add[15:8] = ((x & y) | (x & b[15:8]) | (y & b[15:8])) << 1;
    end
  endfunction
  function [7:0] carry_save_get;
    input [15:0] a;
    begin
      carry_save_get = a[7:0] + a[15:8];
    end
  endfunction
  // inputs
  wire [15:0] e0s0 = {15'b0, din[0 +: 1]};
  wire [15:0] e1s0 = {15'b0, din[1 +: 1]};
  wire [15:0] e2s0 = {15'b0, din[2 +: 1]};
  wire [15:0] e3s0 = {15'b0, din[3 +: 1]};
  wire [15:0] e4s0 = {15'b0, din[4 +: 1]};
  wire [15:0] e5s0 = {15'b0, din[5 +: 1]};
  wire [15:0] e6s0 = {15'b0, din[6 +: 1]};
  wire [15:0] e7s0 = {15'b0, din[7 +: 1]};
  wire [15:0] e8s0 = {15'b0, din[8 +: 1]};
  wire [15:0] e9s0 = {15'b0, din[9 +: 1]};
  wire [15:0] e10s0 = {15'b0, din[10 +: 1]};
  wire [15:0] e11s0 = {15'b0, din[11 +: 1]};
  wire [15:0] e12s0 = {15'b0, din[12 +: 1]};
  wire [15:0] e13s0 = {15'b0, din[13 +: 1]};
  wire [15:0] e14s0 = {15'b0, din[14 +: 1]};
  wire [15:0] e15s0 = {15'b0, din[15 +: 1]};
  wire [15:0] e16s0 = {15'b0, din[16 +: 1]};
  wire [15:0] e17s0 = {15'b0, din[17 +: 1]};
  wire [15:0] e18s0 = {15'b0, din[18 +: 1]};
  wire [15:0] e19s0 = {15'b0, din[19 +: 1]};
  wire [15:0] e20s0 = {15'b0, din[20 +: 1]};
  wire [15:0] e21s0 = {15'b0, din[21 +: 1]};
  wire [15:0] e22s0 = {15'b0, din[22 +: 1]};
  wire [15:0] e23s0 = {15'b0, din[23 +: 1]};
  wire [15:0] e24s0 = {15'b0, din[24 +: 1]};
  wire [15:0] e25s0 = {15'b0, din[25 +: 1]};
  wire [15:0] e26s0 = {15'b0, din[26 +: 1]};
  wire [15:0] e27s0 = {15'b0, din[27 +: 1]};
  wire [15:0] e28s0 = {15'b0, din[28 +: 1]};
  wire [15:0] e29s0 = {15'b0, din[29 +: 1]};
  wire [15:0] e30s0 = {15'b0, din[30 +: 1]};
  wire [15:0] e31s0 = {15'b0, din[31 +: 1]};
  // forward pass
  wire [15:0] e1s1 = carry_save_add(e1s0, e0s0);
  wire [15:0] e3s1 = carry_save_add(e3s0, e2s0);
  wire [15:0] e5s1 = carry_save_add(e5s0, e4s0);
  wire [15:0] e7s1 = carry_save_add(e7s0, e6s0);
  wire [15:0] e9s1 = carry_save_add(e9s0, e8s0);
  wire [15:0] e11s1 = carry_save_add(e11s0, e10s0);
  wire [15:0] e13s1 = carry_save_add(e13s0, e12s0);
  wire [15:0] e15s1 = carry_save_add(e15s0, e14s0);
  wire [15:0] e17s1 = carry_save_add(e17s0, e16s0);
  wire [15:0] e19s1 = carry_save_add(e19s0, e18s0);
  wire [15:0] e21s1 = carry_save_add(e21s0, e20s0);
  wire [15:0] e23s1 = carry_save_add(e23s0, e22s0);
  wire [15:0] e25s1 = carry_save_add(e25s0, e24s0);
  wire [15:0] e27s1 = carry_save_add(e27s0, e26s0);
  wire [15:0] e29s1 = carry_save_add(e29s0, e28s0);
  wire [15:0] e31s1 = carry_save_add(e31s0, e30s0);
  wire [15:0] e3s2 = carry_save_add(e3s1, e1s1);
  wire [15:0] e7s2 = carry_save_add(e7s1, e5s1);
  wire [15:0] e11s2 = carry_save_add(e11s1, e9s1);
  wire [15:0] e15s2 = carry_save_add(e15s1, e13s1);
  wire [15:0] e19s2 = carry_save_add(e19s1, e17s1);
  wire [15:0] e23s2 = carry_save_add(e23s1, e21s1);
  wire [15:0] e27s2 = carry_save_add(e27s1, e25s1);
  wire [15:0] e31s2 = carry_save_add(e31s1, e29s1);
  wire [15:0] e7s3 = carry_save_add(e7s2, e3s2);
  wire [15:0] e15s3 = carry_save_add(e15s2, e11s2);
  wire [15:0] e23s3 = carry_save_add(e23s2, e19s2);
  wire [15:0] e31s3 = carry_save_add(e31s2, e27s2);
  wire [15:0] e15s4 = carry_save_add(e15s3, e7s3);
  wire [15:0] e31s4 = carry_save_add(e31s3, e23s3);
  wire [15:0] e31s5 = carry_save_add(e31s4, e15s4);
  // backward pass
  wire [15:0] e23s6 = carry_save_add(e23s3, e15s4);
  wire [15:0] e11s7 = carry_save_add(e11s2, e7s3);
  wire [15:0] e19s7 = carry_save_add(e19s2, e15s4);
  wire [15:0] e27s7 = carry_save_add(e27s2, e23s6);
  wire [15:0] e5s8 = carry_save_add(e5s1, e3s2);
  wire [15:0] e9s8 = carry_save_add(e9s1, e7s3);
  wire [15:0] e13s8 = carry_save_add(e13s1, e11s7);
  wire [15:0] e17s8 = carry_save_add(e17s1, e15s4);
  wire [15:0] e21s8 = carry_save_add(e21s1, e19s7);
  wire [15:0] e25s8 = carry_save_add(e25s1, e23s6);
  wire [15:0] e29s8 = carry_save_add(e29s1, e27s7);
  wire [15:0] e2s9 = carry_save_add(e2s0, e1s1);
  wire [15:0] e4s9 = carry_save_add(e4s0, e3s2);
  wire [15:0] e6s9 = carry_save_add(e6s0, e5s8);
  wire [15:0] e8s9 = carry_save_add(e8s0, e7s3);
  wire [15:0] e10s9 = carry_save_add(e10s0, e9s8);
  wire [15:0] e12s9 = carry_save_add(e12s0, e11s7);
  wire [15:0] e14s9 = carry_save_add(e14s0, e13s8);
  wire [15:0] e16s9 = carry_save_add(e16s0, e15s4);
  wire [15:0] e18s9 = carry_save_add(e18s0, e17s8);
  wire [15:0] e20s9 = carry_save_add(e20s0, e19s7);
  wire [15:0] e22s9 = carry_save_add(e22s0, e21s8);
  wire [15:0] e24s9 = carry_save_add(e24s0, e23s6);
  wire [15:0] e26s9 = carry_save_add(e26s0, e25s8);
  wire [15:0] e28s9 = carry_save_add(e28s0, e27s7);
  wire [15:0] e30s9 = carry_save_add(e30s0, e29s8);
  // outputs
  assign dout[0 +: 8] = carry_save_get(e0s0);
  assign dout[8 +: 8] = carry_save_get(e1s1);
  assign dout[16 +: 8] = carry_save_get(e2s9);
  assign dout[24 +: 8] = carry_save_get(e3s2);
  assign dout[32 +: 8] = carry_save_get(e4s9);
  assign dout[40 +: 8] = carry_save_get(e5s8);
  assign dout[48 +: 8] = carry_save_get(e6s9);
  assign dout[56 +: 8] = carry_save_get(e7s3);
  assign dout[64 +: 8] = carry_save_get(e8s9);
  assign dout[72 +: 8] = carry_save_get(e9s8);
  assign dout[80 +: 8] = carry_save_get(e10s9);
  assign dout[88 +: 8] = carry_save_get(e11s7);
  assign dout[96 +: 8] = carry_save_get(e12s9);
  assign dout[104 +: 8] = carry_save_get(e13s8);
  assign dout[112 +: 8] = carry_save_get(e14s9);
  assign dout[120 +: 8] = carry_save_get(e15s4);
  assign dout[128 +: 8] = carry_save_get(e16s9);
  assign dout[136 +: 8] = carry_save_get(e17s8);
  assign dout[144 +: 8] = carry_save_get(e18s9);
  assign dout[152 +: 8] = carry_save_get(e19s7);
  assign dout[160 +: 8] = carry_save_get(e20s9);
  assign dout[168 +: 8] = carry_save_get(e21s8);
  assign dout[176 +: 8] = carry_save_get(e22s9);
  assign dout[184 +: 8] = carry_save_get(e23s6);
  assign dout[192 +: 8] = carry_save_get(e24s9);
  assign dout[200 +: 8] = carry_save_get(e25s8);
  assign dout[208 +: 8] = carry_save_get(e26s9);
  assign dout[216 +: 8] = carry_save_get(e27s7);
  assign dout[224 +: 8] = carry_save_get(e28s9);
  assign dout[232 +: 8] = carry_save_get(e29s8);
  assign dout[240 +: 8] = carry_save_get(e30s9);
  assign dout[248 +: 8] = carry_save_get(e31s5);
endmodule
