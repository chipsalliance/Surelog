//////////////////////////////////////////////////////////////////////////////// //
// Filename: 	lfsr.v
//
// Project:	DSP Filtering Example Project
//
// Purpose:	To generate WS bits of an LFSR at each clock step.  The LFSR
//		length is given by the LN parameter, and its internal feedback
//	equation by the TAPS parameter.  The first LN bits out of the register
//	are given by  the INITIAL_VALUE parameter.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017-2019, Gisselquist Technology, LLC
//
// This file is part of the DSP filtering set of designs.
//
// The DSP filtering designs are free RTL designs: you can redistribute them
// and/or modify any of them under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation, either version 3 of
// the License, or (at your option) any later version.
//
// The DSP filtering designs are distributed in the hope that they will be
// useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTIBILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
// General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with these designs.  (It's in the $(ROOT)/doc directory.  Run make
// with no target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	LGPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/lgpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
`ifdef	VERILATOR
`define	WORKS_WITH_VERILATOR
`endif
//
module	lfsr(i_clk, i_reset, i_ce, o_word);
	parameter		WS=24,	// Number of output bits per clock
				LN=8;	// LFSR Register length/polynomial deg
	parameter [(LN-1):0]	TAPS = 8'h2d,
				INITIAL_FILL = { { (LN-1){1'b0}}, 1'b1 };
	//
	input	wire			i_clk, i_reset, i_ce;
	output	wire	[(WS-1):0]	o_word;

	reg	[(LN+WS-2):0]	sreg;

	// Precompute the stepping matrix for k-steps into the future, k<WS.
	// See https://groupgs.google.com/forum/#!topic/sci.crypt/DRrBi2tMocI
	//
	// As for our method, make the synthesis tool do our work for us.  This
	// works because we are giving the tool constants, and expressions
	// derived from constants.

	// Verilat*r has a problem with tapv: it depends upon itself, and so
	// verilat*r cannot optimize it.  We'll tell Verilator to ignore this
	// problem for now (it'll still do the "right thing"), but we're not
	// going to get wonderful code from Verilator as a result.
	//
	// verilator lint_off UNOPTFLAT
	wire	[(LN-1):0]	tapv	[0:(WS-1)];
	assign	tapv[0] = TAPS;

	genvar	k;
	generate for(k=1; k<WS; k=k+1)
	begin : PRECALCULATING_TAP_VALUE
		assign	tapv[k] = (tapv[k-1]<<1)^((tapv[k-1][(LN-1)])?TAPS:0);
	end endgenerate
	// verilator lint_on  UNOPTFLAT

	// The trick to this approach is to calculate the reset value.
	// Upon reset, we want the bottom LN bits to be our INITIAL_FILL.
	// The problem is that each bit from there on up is determined from
	// the LN-1 bits before it.  That means we need to do some work
	// to make certain our reset_value is valid.
	//
	// The good news is that the synthesis tool should be able to do this
	// work for us.
`ifdef	WORKS_WITH_VERILATOR
	reg	[(LN+WS-2):0]	reset_value;
	initial	reset_value[(LN-1):0] = INITIAL_FILL;
	generate
	for(k=0; k<WS-1; k=k+1)
		initial	reset_value[(LN+k)] = ^(reset_value[(LN+k-1):k]&TAPS);
	endgenerate
`else
	wire	[(LN+WS-2):0]	reset_value;
	assign	reset_value[(LN-1):0] = INITIAL_FILL;
	generate
	for(k=0; k<WS-1; k=k+1)
	begin : CALC_RESET
		assign	reset_value[(LN+k)] = ^(reset_value[ k +: LN]&TAPS);
	end endgenerate
`endif

	// Step the actual shift register.  First, step the shifted parts of
	// the register
	//
`ifdef	WORKS_WITH_VERILATOR
	initial	sreg = reset_value;
`else
	initial	sreg = (INITIAL_FILL<<WS);
`endif
	always @(posedge i_clk)
		if (i_reset)
			sreg[(LN-2):0] <= reset_value[(LN-2):0];
		else if (i_ce)
			sreg[(LN-2):0] <= sreg[(LN+WS-2):WS];

	//
	// Then calculate the parts that are not shifted.
	//
	generate
	for(k=0; k<WS; k = k+1)
	begin : RUN_LFSR
		always @(posedge i_clk)
			if (i_reset)
				sreg[LN+k-1] <= reset_value[LN+k-1];
			else if (i_ce)
				sreg[(LN+k-1)] <=
					^(sreg[(LN+WS-2):(WS-1)]&tapv[k]);
	end endgenerate

	assign	o_word = sreg[(WS-1):0];

`ifdef	FORMAL

`ifdef	LFSR
	reg	f_last_clk;

	initial	assume(!i_clk);
	initial	assume(f_last_clk);
	always @($global_clock)
	begin
		assume(i_clk == !f_last_clk);
		f_last_clk = i_clk;
	end

	initial	assume(i_reset);
`endif

	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid = 1'b1;

	always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_reset)))
			assert(sreg[(LN-1):0] == INITIAL_FILL);

	//
	// We should be able to re-apply our transform, as defined by TAPS,
	// to any of our output bits to make certain that the transform
	// still defines the "next" bit--no matter which bit that is.

	// First, for the last bit out
	always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_reset))&&($past(i_ce)))
			assert(sreg[LN-1]
				== ^({sreg[(LN-2):0], $past(sreg[WS-1])}
					& TAPS));
	generate
	for(k=0; k<WS-1; k=k+1)
		always @(posedge i_clk)
			if ((f_past_valid)&&(!$past(i_reset)))
			assert(sreg[LN+k] == ^(sreg[(LN-1+k):k]&TAPS));
	endgenerate

	// The shift register is never allowed to become zero, lest it get
	// stuck and produce nothing but zero outputs.
	always @(*)
		assert(sreg[(LN+WS-2):(WS-1)] != 0);

`endif
endmodule
