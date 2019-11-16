////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	genericfir.v
//
// Project:	DSP Filtering Example Project
//
// Purpose:	Implement a high speed (1-output per clock), adjustable tap FIR
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
//
module	genericfir(i_clk, i_reset, i_tap_wr, i_tap, i_ce, i_sample, o_result);
	parameter		NTAPS=128, IW=12, TW=IW, OW=2*IW+7;
	parameter [0:0]		FIXED_TAPS=0;
	input	wire			i_clk, i_reset;
	//
	input	wire			i_tap_wr;	// Ignored if FIXED_TAPS
	input	wire	[(TW-1):0]	i_tap;		// Ignored if FIXED_TAPS
	//
	input	wire			i_ce;
	input	wire	[(IW-1):0]	i_sample;
	output	wire	[(OW-1):0]	o_result;

	wire	[(TW-1):0] tap		[NTAPS:0];
	wire	[(TW-1):0] tapout	[NTAPS:0];
	wire	[(IW-1):0] sample	[NTAPS:0];
	wire	[(OW-1):0] result	[NTAPS:0];
	wire		tap_wr;

	// The first sample in our sample chain is the sample we are given
	assign	sample[0]	= i_sample;
	// Initialize the partial summing accumulator with zero
	assign	result[0]	= 0;

	genvar	k;
	generate
	if(FIXED_TAPS)
	begin
		initial $readmemh("taps.hex", tap);

		assign	tap_wr = 1'b0;
	end else begin
		assign	tap_wr = i_tap_wr;
		assign	tap[0] = i_tap;
	end

	for(k=0; k<NTAPS; k=k+1)
	begin: FILTER

		firtap #(.FIXED_TAPS(FIXED_TAPS),
				.IW(IW), .OW(OW), .TW(TW),
				.INITIAL_VALUE(0))
			tapk(i_clk, i_reset,
				// Tap update circuitry
				tap_wr, tap[NTAPS-1-k], tapout[k],
				// Sample delay line
				i_ce, sample[k], sample[k+1],
				// The output accumulator
				result[k], result[k+1]);

		if (!FIXED_TAPS)
			assign	tap[NTAPS-1-k] = tapout[k+1];

		// Make verilator happy
		// verilator lint_off UNUSED
		wire	[(TW-1):0]	unused_tap;
		if (FIXED_TAPS)
			assign	unused_tap    = tapout[k];
		// verilator lint_on UNUSED
	end endgenerate

	assign	o_result = result[NTAPS];

	// Make verilator happy
	// verilator lint_off UNUSED
	wire	[(TW):0]	unused;
	assign	unused = { i_tap_wr, i_tap };
	// verilator lint_on UNUSED

endmodule

