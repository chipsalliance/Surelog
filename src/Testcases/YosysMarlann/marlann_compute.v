/*
 *  Copyright (C) 2018  Clifford Wolf <clifford@symbioticeda.com>
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

module marlann_compute #(
	parameter integer NB = 2,
	parameter integer CODE_SIZE = 512,
	parameter integer COEFF_SIZE = 512
) (
	input         clock,
	input         reset,
	output        busy,

	input         cmd_valid,
	output        cmd_ready,
	input  [31:0] cmd_insn,

	output        mem_ren,
	output [ 7:0] mem_wen,
	output [15:0] mem_addr,
	output [63:0] mem_wdata,
	input  [63:0] mem_rdata,

	output        tick_simd,
	output        tick_nosimd
);
	integer i;

	reg [31:0] code_mem [0:CODE_SIZE-1];
	reg [64*NB-1:0] coeff_mem [0:COEFF_SIZE-1];

	reg [31:0] acc0, acc1;

	reg [16:0] VBP, LBP, SBP;
	reg [ 8:0] CBP;

	reg        mem_rd0_en;
	reg [15:0] mem_rd0_addr;

	reg        mem_rd1_en;
	reg [15:0] mem_rd1_addr;

	reg [ 7:0] mem_wr_en;
	reg [15:0] mem_wr_addr;
	reg [63:0] mem_wr_wdata;

	assign mem_ren = mem_rd0_en || mem_rd1_en;
	assign mem_wen = mem_wr_en;
	assign mem_addr = ({16{mem_rd0_en}} & mem_rd0_addr) | ({16{mem_rd1_en}} & mem_rd1_addr) | ({16{|mem_wr_en}} & mem_wr_addr);
	assign mem_wdata = mem_wr_wdata;

	wire [16:0] cmd_insn_maddr = cmd_insn[31:15];
	wire [8:0] cmd_insn_caddr = cmd_insn[14:6];
	wire [5:0] cmd_insn_opcode = cmd_insn[5:0];


	/**** staging ****/

	reg                 s1_en;
	wire [        31:0] s1_insn;
	wire                s1_stall;

	reg                 s2_en;
	reg  [        31:0] s2_insn;

	reg                 s3_en;
	reg  [        31:0] s3_insn;

	reg                 s3a_en;
	reg  [        31:0] s3a_insn;

	reg                 s4_en;
	reg  [        31:0] s4_insn;
	reg  [   NB*64-1:0] s4_coeff;

	reg                 s5_en;
	reg  [        31:0] s5_insn;
	reg  [     8*9-1:0] s5_max;

	reg                 s6_en;
	reg  [        31:0] s6_insn;
	reg  [     4*9-1:0] s6_max;

	reg                 s7_en;
	reg  [        31:0] s7_insn;
	wire [  NB*128-1:0] s7_prod;
	reg  [     2*9-1:0] s7_max;

	reg                 s8_en;
	reg  [        31:0] s8_insn;
	reg  [        19:0] s8_sum0;
	reg  [        19:0] s8_sum1;
	reg  [         8:0] s8_max;
	reg                 s8_maxen;

	reg                 s9_en;
	reg  [        31:0] s9_insn;


	/**** memory and max interlock ****/

	reg [9:0] memlock_res;
	reg [9:0] memlock_mask;
	reg memlock_expect;

	always @* begin
		memlock_mask = 0;

		case (s1_insn[5:0])
			/* LoadCode, LoadCoeff0, LoadCoeff1 */
			4, 5, 6: memlock_mask = 1 << 0;

			/* LdSet, LdSet0, LdSet1, LdAdd, LdAdd0, LdAdd1 */
			28, 29, 30, 32, 33, 34: begin
				memlock_mask = 1 << 4;
			end

			/* MACC, MMAX, MACCZ, MMAXZ, MMAXN */
			40, 41, 42, 43, 45: memlock_mask = 1 << 0;

			/* Store, Store0, Store1, ReLU, ReLU0, ReLU1, Save, Save0, Save1 */
			16, 17, 18, 20, 21, 22, 24, 25, 26: memlock_mask = 1 << 9;
		endcase

		if (!s1_en || reset)
			memlock_mask = 0;
	end

	reg maxlock_a;
	reg maxlock_b;
	reg maxlock_a_q;

	always @* begin
		maxlock_a = 0;
		maxlock_b = 0;

		case (s1_insn[5:0] & 6'b 1111_00)
			28, 32, 40, 44: maxlock_a = 1;
		endcase

		case (s1_insn[5:0])
			41, 43, 45, 47: maxlock_b = 1;
		endcase

		if (!s1_en || reset) begin
			maxlock_a = 0;
			maxlock_b = 0;
		end
	end

	assign s1_stall = |(memlock_res & memlock_mask) || (maxlock_b && maxlock_a_q);

	always @(posedge clock) begin
		{memlock_res, memlock_expect} <= memlock_res | (s1_stall ? 10'b 0 : memlock_mask);
		maxlock_a_q <= maxlock_a && !s1_stall;

		if (reset) begin
			memlock_res <= 0;
			memlock_expect <= 0;
			maxlock_a_q <= 0;
		end
	end

	assign cmd_ready = !s1_stall;

	assign busy = |{s1_en, s2_en, s3_en, s4_en, s5_en, s6_en, s7_en, s8_en};


	/**** stage 1 ****/

	reg [31:0] s1_insn_direct;
	reg [31:0] s1_insn_codemem;
	reg s1_insn_sel;

	assign s1_insn = s1_insn_sel ? s1_insn_codemem : s1_insn_direct;

	wire [16:0] s1_insn_maddr = s1_insn[31:15];
	wire [8:0] s1_insn_caddr = s1_insn[14:6];
	wire [5:0] s1_insn_opcode = s1_insn[5:0];

	always @(posedge clock) begin
		if (!s1_stall) begin
			s1_en <= cmd_valid && cmd_ready;
			s1_insn_direct <= cmd_insn;
			s1_insn_codemem <= code_mem[cmd_insn[14:6]];
			s1_insn_sel <= cmd_insn[5:0] == 3;
		end

		if (reset) begin
			s1_en <= 0;
		end
	end


	/**** stage 2 ****/

	reg s2_tick_simd;

	always @(posedge clock) begin
		s2_en <= 0;
		s2_insn <= s1_insn;
		s2_tick_simd <= 0;

		mem_rd0_en <= 0;
		mem_rd0_addr <= 'bx;

		if (!reset && s1_en && !s1_stall) begin
			s2_en <= 1;

			case (s1_insn[5:0])
				/* LoadCode, LoadCoeff0, LoadCoeff1 */
				4, 5, 6: begin
					mem_rd0_en <= 1;
					mem_rd0_addr <= s1_insn[31:15] >> 1;
				end

				/* SetVBP, AddVBP */
				8, 9: begin
					VBP <= s1_insn[31:15] + (s1_insn[0] ? VBP : 0);
				end

				/* MACC, MMAX, MACCZ, MMAXZ, MMAXN */
				40, 41, 42, 43, 45: begin
					mem_rd0_en <= 1;
					mem_rd0_addr <= (s1_insn[31:15] + VBP) >> 1;
					s2_tick_simd <= 1;
				end
			endcase
		end
	end

	assign tick_simd = s2_tick_simd;
	assign tick_nosimd = s2_en && !tick_simd;


	/**** stage 3 ****/

	always @(posedge clock) begin
		s3_en <= 0;
		s3_insn <= s2_insn;

		if (!reset && s2_en) begin
			s3_en <= 1;
		end
	end


	/**** stage 3A ****/

	always @(posedge clock) begin
		s3a_en <= 0;
		s3a_insn <= s3_insn;

		if (!reset && s3_en) begin
			s3a_en <= 1;
		end
	end


	/**** stage 4 ****/

	always @(posedge clock) begin
		s4_en <= 0;
		s4_insn <= s3a_insn;
		s4_coeff <= coeff_mem[s3a_insn[14:6] + CBP];

		if (!reset && s3a_en) begin
			s4_en <= 1;

			/* SetCBP, AddCBP */
			if (s3a_insn[5:0] == 14 || s3a_insn[5:0] == 15) begin
				CBP <= s3a_insn[14:6] + (s3a_insn[0] ? CBP : 0);
			end
		end
	end


	/**** stage 5 ****/

	always @(posedge clock) begin
		s5_en <= 0;
		s5_insn <= s4_insn;

		s5_max[0*9 +: 9] <= s4_coeff[0*8 +: 8] ? $signed(mem_rdata[0*8 +: 8]) : 9'h100;
		s5_max[1*9 +: 9] <= s4_coeff[1*8 +: 8] ? $signed(mem_rdata[1*8 +: 8]) : 9'h100;
		s5_max[2*9 +: 9] <= s4_coeff[2*8 +: 8] ? $signed(mem_rdata[2*8 +: 8]) : 9'h100;
		s5_max[3*9 +: 9] <= s4_coeff[3*8 +: 8] ? $signed(mem_rdata[3*8 +: 8]) : 9'h100;
		s5_max[4*9 +: 9] <= s4_coeff[4*8 +: 8] ? $signed(mem_rdata[4*8 +: 8]) : 9'h100;
		s5_max[5*9 +: 9] <= s4_coeff[5*8 +: 8] ? $signed(mem_rdata[5*8 +: 8]) : 9'h100;
		s5_max[6*9 +: 9] <= s4_coeff[6*8 +: 8] ? $signed(mem_rdata[6*8 +: 8]) : 9'h100;
		s5_max[7*9 +: 9] <= s4_coeff[7*8 +: 8] ? $signed(mem_rdata[7*8 +: 8]) : 9'h100;

		mem_rd1_en <= 0;
		mem_rd1_addr <= 'bx;

		if (!reset && s4_en) begin
			s5_en <= 1;

			case (s4_insn[5:0])
				/* LoadCode */
				4: begin
					code_mem[s4_insn[14:6]] <= mem_rdata[31:0];
				end

				/* LoadCoeff0 */
				5: begin
					coeff_mem[s4_insn[14:6]][63:0] <= mem_rdata;
				end

				/* LoadCoeff1 */
				6: begin
					coeff_mem[s4_insn[14:6]][127:64] <= mem_rdata;
				end

				/* SetLBP, AddLBP */
				10, 11: begin
					LBP <= s4_insn[31:15] + (s4_insn[0] ? LBP : 0);
				end

				/* LdSet, LdSet0, LdSet1, LdAdd, LdAdd0, LdAdd1 */
				28, 29, 30, 32, 33, 34: begin
					mem_rd1_en <= 1;
					mem_rd1_addr <= (s4_insn[31:15] + LBP) >> 1;
				end
			endcase
		end
	end


	/**** stage 6 ****/

	always @(posedge clock) begin
		s6_en <= 0;
		s6_insn <= s5_insn;

		s6_max[0*9 +: 9] <= $signed(s5_max[0*9 +: 9]) > $signed(s5_max[1*9 +: 9]) ? s5_max[0*9 +: 9] : s5_max[1*9 +: 9];
		s6_max[1*9 +: 9] <= $signed(s5_max[2*9 +: 9]) > $signed(s5_max[3*9 +: 9]) ? s5_max[2*9 +: 9] : s5_max[3*9 +: 9];
		s6_max[2*9 +: 9] <= $signed(s5_max[4*9 +: 9]) > $signed(s5_max[5*9 +: 9]) ? s5_max[4*9 +: 9] : s5_max[5*9 +: 9];
		s6_max[3*9 +: 9] <= $signed(s5_max[6*9 +: 9]) > $signed(s5_max[7*9 +: 9]) ? s5_max[6*9 +: 9] : s5_max[7*9 +: 9];

		if (!reset && s5_en) begin
			s6_en <= 1;
		end
	end


	/**** stage 7 ****/

	wire [NB*64-1:0] mulA = {mem_rdata, mem_rdata};

	marlann_compute_mul2 mul [NB*4-1:0] (
		.clock (clock   ),
		.A     (mulA    ),
		.B     (s4_coeff),
		.X     (s7_prod )
	);

	always @(posedge clock) begin
		s7_en <= 0;
		s7_insn <= s6_insn;

		s7_max[0*9 +: 9] <= $signed(s6_max[0*9 +: 9]) > $signed(s6_max[1*9 +: 9]) ? s6_max[0*9 +: 9] : s6_max[1*9 +: 9];
		s7_max[1*9 +: 9] <= $signed(s6_max[2*9 +: 9]) > $signed(s6_max[3*9 +: 9]) ? s6_max[2*9 +: 9] : s6_max[3*9 +: 9];

		if (!reset && s6_en) begin
			s7_en <= 1;
		end
	end


	/**** stage 8 ****/

	reg [31:0] acc0zn;

	always @* begin
		acc0zn = s7_insn[1] ? 0 : acc0;
		acc0zn = s7_insn[2] ? 32'h 8000_0000 : acc0zn;
	end

	always @(posedge clock) begin
		s8_en <= 0;
		s8_insn <= s7_insn;

		s8_sum0 <= $signed(s7_prod[  0 +: 16]) + $signed(s7_prod[ 16 +: 16]) + $signed(s7_prod[ 32 +: 16]) + $signed(s7_prod[ 48 +: 16]) +
		           $signed(s7_prod[ 64 +: 16]) + $signed(s7_prod[ 80 +: 16]) + $signed(s7_prod[ 96 +: 16]) + $signed(s7_prod[112 +: 16]);

		s8_sum1 <= $signed(s7_prod[128 +: 16]) + $signed(s7_prod[144 +: 16]) + $signed(s7_prod[160 +: 16]) + $signed(s7_prod[176 +: 16]) +
		           $signed(s7_prod[192 +: 16]) + $signed(s7_prod[208 +: 16]) + $signed(s7_prod[224 +: 16]) + $signed(s7_prod[240 +: 16]);

		s8_max <= $signed(s7_max[0*9 +: 9]) > $signed(s7_max[1*9 +: 9]) ? s7_max[0*9 +: 9] : s7_max[1*9 +: 9];
		s8_maxen <= ($signed(s7_max[0*9 +: 9]) > $signed(acc0zn)) || ($signed(s7_max[1*9 +: 9]) > $signed(acc0zn));

		if (!reset && s7_en) begin
			s8_en <= 1;
		end
	end


	/**** stage 9 ****/

	reg [31:0] new_acc0_add;
	reg [31:0] new_acc1_add;

	reg [31:0] new_acc0_max;

	reg [31:0] new_acc0;
	reg [31:0] new_acc1;

	wire [31:0] acc0_shifted = $signed(acc0) >>> s8_insn[14:6];
	wire [31:0] acc1_shifted = $signed(acc1) >>> s8_insn[14:6];

	reg [7:0] acc0_saturated;
	reg [7:0] acc1_saturated;

	reg new_acc0_max_cmp;
	reg new_acc0_max_cmp_q;

	always @* begin
		new_acc0_add = s8_insn[1] ? 0 : acc0;
		new_acc1_add = s8_insn[1] || s8_insn[2] ? 0 : acc1;

		new_acc0_max = s8_insn[2] ? 32'h 8000_0000 : new_acc0_add;

		new_acc0_add = $signed(new_acc0_add) + $signed(s8_sum0);
		new_acc1_add = $signed(new_acc1_add) + $signed(s8_sum1);

		if (s8_max != 9'h 100)
			new_acc0_max = s8_maxen ? s8_max : new_acc0_max;

		new_acc0 = s8_insn[0] ? new_acc0_max : new_acc0_add;
		new_acc1 = new_acc1_add;
	end

	always @(posedge clock) begin
		s9_en <= 0;
		s9_insn <= s8_insn;

		if (!reset && s8_en) begin
			s9_en <= 1;

			/* MACC, MMAX, MMACZ, MMAXZ, MMAXN */
			if (s8_insn[5:3] == 3'b 101) begin
				acc0 <= new_acc0;
				acc1 <= new_acc1;
			end

			/* LdSet, LdSet0 */
			if (s8_insn[5:0] == 28 || s8_insn[5:0] == 29) begin
				acc0 <= mem_rdata[31:0];
			end

			/* LdSet, LdSet1 */
			if (s8_insn[5:0] == 28 || s8_insn[5:0] == 30) begin
				acc1 <= mem_rdata[63:32];
			end

			/* LdAdd, LdAdd0 */
			if (s8_insn[5:0] == 32 || s8_insn[5:0] == 33) begin
				acc0 <= acc0 + mem_rdata[31:0];
			end

			/* LdAdd, LdAdd1 */
			if (s8_insn[5:0] == 32 || s8_insn[5:0] == 34) begin
				acc1 <= acc1 + mem_rdata[63:32];
			end
		end

		if (&acc0_shifted[31:7] == |acc0_shifted[31:7])
			acc0_saturated <= acc0_shifted[7:0];
		else
			acc0_saturated <= acc0_shifted[31] ? -128 : 127;

		if (&acc1_shifted[31:7] == |acc1_shifted[31:7])
			acc1_saturated <= acc1_shifted[7:0];
		else
			acc1_saturated <= acc1_shifted[31] ? -128 : 127;
	end


	/**** write back ****/

	reg [ 7:0] pre_mem_wr_en;
	reg [16:0] pre_mem_wr_addr;
	reg [63:0] pre_mem_wr_wdata;

	always @* begin
		if (pre_mem_wr_addr[0]) begin
			mem_wr_en = pre_mem_wr_en << 1;
			mem_wr_addr = pre_mem_wr_addr >> 1;
			mem_wr_wdata = pre_mem_wr_wdata << 8;
		end else begin
			mem_wr_en = pre_mem_wr_en;
			mem_wr_addr = pre_mem_wr_addr >> 1;
			mem_wr_wdata = pre_mem_wr_wdata;
		end
	end

	wire [5:0] s9_insn_opcode = s9_insn[5:0];

	always @(posedge clock) begin
		pre_mem_wr_en <= 0;
		pre_mem_wr_addr <= s9_insn[31:15] + SBP;
		pre_mem_wr_wdata <= {
			{8{!s9_insn[2] || !acc1_saturated[7]}} & acc1_saturated,
			{8{!s9_insn[2] || !acc0_saturated[7]}} & acc0_saturated
		};

		if (s9_en) begin
			/* Store, Store0, Store1, ReLU, ReLU0, ReLU1 */
			if (s9_insn[5:3] == 3'b 010) begin
				pre_mem_wr_en <= {!s9_insn[0], !s9_insn[1]};
			end

			/* Save, Save0, Save1 */
			if (s9_insn[5:2] == 4'b 0110) begin
				pre_mem_wr_en <= {{4{!s9_insn[0]}}, {4{!s9_insn[1]}}};
				pre_mem_wr_wdata <= {acc1, acc0};
			end

			/* SetSBP, AddSBP */
			if (s9_insn[5:0] == 12 || s9_insn[5:0] == 13) begin
				SBP <= s9_insn[31:15] + (s9_insn[0] ? SBP : 0);
			end
		end

		if (reset || !s9_en) begin
			pre_mem_wr_en <= 0;
		end
	end
endmodule

module marlann_compute_mul2 (
	input         clock,
	input  [15:0] A, B,
	output [31:0] X
);
	reg [15:0] r1A, r2A, r3A;
	reg [15:0] r1B, r2B, r3B;

	always @(posedge clock) begin
		r1A <= $signed(A[7:0]) * $signed(B[7:0]);
		r1B <= $signed(A[15:8]) * $signed(B[15:8]);
		r2A <= r1A;
		r2B <= r1B;
		r3A <= r2A;
		r3B <= r2B;
	end

	assign X = {r3B, r3A};
endmodule
