// Formal Verification with SymbiYosys:
//   sby -f shifter64.sby default
//   sby -f shifter64.sby nofslrw
//   sby -f shifter64.sby nowmode
//
// Area estimate with Yosys:
//   yosys -p "synth -top shifter64 -flatten; abc -g cmos2; stat" shifter64.v
//   yosys -D NO_FSLRW -p "synth -top shifter64 -flatten; abc -g cmos2; stat" shifter64.v
//   yosys -D NO_WMODE -p "synth -top shifter64 -flatten; abc -g cmos2; stat" shifter64.v
//
//               default nofslrw nowmode
//        LUT-4      680     680     707
//        LUT-6      386     386     427
//        Gates     2118    2105    2084
//
//        NAND      1851    1837    1693
//        NOR        238     259     380
//        NOT         59      18      22
//
//   (NOT = 1/2 gate, use "abc -lut 4" or "abc -lut 6" for LUT counts)

module shifter64 (
	input [63:0] A, B,
	output [63:0] X,
	input [6:0] shamt,
	input insn30,
	input insn29,
	input insn26,
	input insn14,
	input insn3
);
`ifdef NO_WMODE
	wire wmode = 0;
`else
	wire wmode = insn3;
`endif
	reg [63:0] bb;
	reg [6:0] sh;

	always @* begin
		sh = shamt;
		bb = B;

		if (wmode || !insn26)
			sh[6] = 0;

`ifdef NO_FSLRW
		if (wmode)
			sh[5] = 0;
`else
		if (wmode && !insn26)
			sh[5] = 0;
`endif

		if (insn14)
			sh = -sh;

		if (!insn26) begin
			casez ({insn30, insn29})
				2'b 0z: bb = {64{insn29}};
				2'b 10: bb = {64{wmode ? A[31] : A[63]}};
				2'b 11: bb = A;
			endcase
		end
	end
	
	shifter64_datapath datapath (
		.A     (A    ),
		.B     (bb   ),
		.X     (X    ),
		.shamt (sh   ),
		.wmode (wmode)
	);
endmodule

module shifter64_datapath (
	input [63:0] A, B,
	output [63:0] X,
	input [6:0] shamt,
	input wmode
);
	reg [127:0] tmp, tmp2;

	wire shamt_5_0 = wmode ? 0 : shamt[5];
	wire shamt_5_1 = wmode ? 1 : shamt[5];
	wire shamt_5_2 = wmode ? 0 : shamt[5];
	wire shamt_5_3 = wmode ? 1 : shamt[5];

	wire shamt_6_0 = wmode ?  shamt[5] : shamt[6];
	wire shamt_6_1 = wmode ? !shamt[5] : shamt[6];
	wire shamt_6_2 = wmode ? !shamt[5] : shamt[6];
	wire shamt_6_3 = wmode ?  shamt[5] : shamt[6];

	always @* begin
		tmp = {B, A};

`ifdef NO_WMODE
		if (shamt[5]) tmp = {tmp[95:0], tmp[127:96]};
		if (shamt[6]) tmp = {tmp[63:0], tmp[127:64]};
`else
		tmp2 = tmp;
		if (shamt_5_0) tmp2[ 31: 0] = tmp[127:96];
		if (shamt_5_1) tmp2[ 63:32] = tmp[ 31: 0];
		if (shamt_5_2) tmp2[ 95:64] = tmp[ 63:32];
		if (shamt_5_3) tmp2[127:96] = tmp[ 95:64];

		tmp = tmp2;
		if (shamt_6_0) tmp[ 31: 0] = tmp2[ 95:64];
		if (shamt_6_1) tmp[ 63:32] = tmp2[127:96];
		if (shamt_6_2) tmp[ 95:64] = tmp2[ 31: 0];
		if (shamt_6_3) tmp[127:96] = tmp2[ 63:32];
`endif
		if (shamt[4]) tmp = {tmp[111:0], tmp[127:112]};
		if (shamt[3]) tmp = {tmp[119:0], tmp[127:120]};
		if (shamt[2]) tmp = {tmp[123:0], tmp[127:124]};
		if (shamt[1]) tmp = {tmp[125:0], tmp[127:126]};
		if (shamt[0]) tmp = {tmp[126:0], tmp[127:127]};
	end

	assign X = tmp;
endmodule

`ifdef FORMAL
module shifter64_props (
	input [63:0] A, B,
	output [63:0] X,
	input [6:0] shamt,
	input insn30,
	input insn29,
	input insn26,
	input insn14,
	input insn3
);
	shifter64 uut (
		.A      (A     ),
		.B      (B     ),
		.X      (X     ),
		.shamt  (shamt ),
		.insn30 (insn30),
		.insn29 (insn29),
		.insn26 (insn26),
		.insn14 (insn14),
		.insn3  (insn3 )
	);

	wire [31:0] AL = A;
	wire [31:0] BL = B;
	wire [31:0] XL = X;

	wire [6:0] sh7 = shamt;
	wire [5:0] sh6 = shamt;
	wire [4:0] sh5 = shamt;

	wire [63:0] X_SLL = A << sh6;
	wire [63:0] X_SRL = A >> sh6;
	wire [63:0] X_SRA = $signed(A) >>> sh6;
	wire [63:0] X_SLO = ~(~A << sh6);
	wire [63:0] X_SRO = ~(~A >> sh6);
	wire [63:0] X_ROL = ({A,A} << sh6) >> 64;
	wire [63:0] X_ROR = ({A,A} >> sh6);
	wire [63:0] X_FSL = ({A,B,A,B} << sh7) >> (64+128);
	wire [63:0] X_FSR = ({B,A,B,A} >> sh7);

	wire [31:0] X_SLLW = AL << sh5;
	wire [31:0] X_SRLW = AL >> sh5;
	wire [31:0] X_SRAW = $signed(AL) >>> sh5;
	wire [31:0] X_SLOW = ~(~AL << sh5);
	wire [31:0] X_SROW = ~(~AL >> sh5);
	wire [31:0] X_ROLW = ({AL,AL} << sh5) >> 32;
	wire [31:0] X_RORW = ({AL,AL} >> sh5);
	wire [31:0] X_FSLW = ({AL,BL,AL,BL} << sh6) >> (32+64);
	wire [31:0] X_FSRW = ({BL,AL,BL,AL} >> sh6);

	always @* begin
		casez ({insn30, insn29, insn26, insn14, insn3})
			5'b 00000: assert(X == X_SLL);
			5'b 00010: assert(X == X_SRL);
			5'b 10010: assert(X == X_SRA);
			5'b 01000: assert(X == X_SLO);
			5'b 01010: assert(X == X_SRO);
			5'b 11000: assert(X == X_ROL);
			5'b 11000: assert(X == X_ROR);
			5'b zz100: assert(X == X_FSL);
			5'b zz110: assert(X == X_FSR);

`ifndef NO_WMODE
			5'b 00001: assert(XL == X_SLLW);
			5'b 00011: assert(XL == X_SRLW);
			5'b 10011: assert(XL == X_SRAW);
			5'b 01001: assert(XL == X_SLOW);
			5'b 01011: assert(XL == X_SROW);
			5'b 11001: assert(XL == X_ROLW);
			5'b 11001: assert(XL == X_RORW);
  `ifndef NO_FSLRW
			5'b zz101: assert(XL == X_FSLW);
			5'b zz111: assert(XL == X_FSRW);
  `endif
`endif
		endcase
	end
endmodule
`endif
