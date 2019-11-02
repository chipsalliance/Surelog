////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	shalfband.v
//
// Project:	DSP Filtering Example Project
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2018-2019, Gisselquist Technology, LLC
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
module	shalfband(i_clk, i_reset, i_tap_wr, i_tap, i_ce, i_sample, o_ce, o_result);
	parameter			LGNTAPS = 7, IW=16, TW=12,
					OW = IW+TW+LGNTAPS;
	parameter	[LGNTAPS:0]	NTAPS = 107;
	parameter	[0:0]		FIXED_TAPS = 1'b0;
	parameter			INITIAL_COEFFS  = "";
	parameter	[0:0]		OPT_HILBERT = 1'b0;
	// // //
	localparam			LGNMEM   = LGNTAPS-1,
					LGNCOEF  = LGNMEM-1;
	localparam	[LGNTAPS-1:0]	HALFTAPS = NTAPS[LGNTAPS:1];
	localparam	[LGNTAPS-2:0]	QTRTAPS = HALFTAPS[LGNTAPS-1:1]+1;
	localparam			DMEMSZ = (1<<LGNMEM);
	localparam			CMEMSZ = (1<<LGNCOEF);

/*
initial assert(NTAPS[2:0] == 3'h7);
*/

/*
always @(*)
	assert(NTAPS[2:0] == 3'h7);
*/

/*
always @(posedge i_clk)
	assert(NTAPS[2:0] == 3'h7);
*/


	//
	// Control inputs (wires)
	input	wire		i_clk, i_reset;
	//
	// Coefficient control -- allows you to update coefficients in the
	// filter
	input	wire			i_tap_wr;
	input	wire	[(TW-1):0]	i_tap;
	//
	// New sample input(s)--a new sample comes in any time i_ce is true.
	// There must be at least NTAPS idle's between every pair of valid
	// i_ce's.
	input	wire			i_ce;
	input	wire	[(IW-1):0]	i_sample;
	//
	// The output--valid any time o_ce is true.  Since it only changes
	// once per interval, you can ignore the o_ce line if you choose and
	// just use i_ce.
	output	reg			o_ce;
	output	reg	[(OW-1):0]	o_result;
	//
	//

	reg	[(TW-1):0]	tapmem	[0:(CMEMSZ-1)];	// Coef memory
	reg signed [(TW-1):0]	tap;		// Value read from coef memory

	reg	[(LGNMEM-1):0]	dwidx, lidx, ridx;// Data write and read indices
	reg	[(LGNCOEF-1):0]	tidx;		// Coefficient read index
	reg	[(IW-1):0]	dmem1	[0:(DMEMSZ-1)];	// Data memory
	reg	[(IW-1):0]	dmem2	[0:(DMEMSZ-1)];	// Data memory
	// Data value read from memory, and then summed together
	reg signed [(IW-1):0]	dleft, dright, mid_sample;
	reg signed [IW:0]	dsum;

	// Traveling CE values
	reg	m_ce, d_ce, s_ce;
	//
	// The product and accumulator values for the filter
	reg	signed [(IW+TW-1):0]	product;
	reg	signed [(OW-1):0]	r_acc;

	//
	//
	// Allow the user to set the taps
	//
	//

	// Starting at zero on reset, increment the tap write index on any
	// write of a new tap.  This also means that changing coefficients
	// will require a reset.
	generate if (FIXED_TAPS)
	begin : SET_FIXED_TAPS
		initial $readmemh(INITIAL_COEFFS, tapmem);

		// Make Verilators -Wall happy
		// Verilator lint_off UNUSED
		wire	[TW:0]	ignored_inputs;
		assign	ignored_inputs = { i_tap_wr, i_tap };
		// Verilator lint_on  UNUSED
	end else begin : DYNAMIC_TAP_ADJUSTMENT
		// Coef memory write index
		reg	[(LGNCOEF-1):0]	tapwidx;

		initial	tapwidx = 0;
		always @(posedge i_clk)
			if(i_reset)
				tapwidx <= 0;
			else if (i_tap_wr)
				tapwidx <= tapwidx + 1'b1;

		if (INITIAL_COEFFS != 0)
			initial $readmemh(INITIAL_COEFFS, tapmem);
		always @(posedge i_clk)
			if (i_tap_wr)
				tapmem[tapwidx] <= i_tap;
	end endgenerate


	//
	//
	// Record the incoming data into a local memory
	//
	//

	// Notice how this data writing section is *independent* of the reset,
	// depending only upon new sample data.
	initial	dwidx = 0;
	always @(posedge i_clk)
	if (i_ce)
		dwidx <= dwidx + 1'b1;
	always @(posedge i_clk)
	if (i_ce)
		dmem1[dwidx] <= i_sample;
	always @(posedge i_clk)
	if (i_ce)
		dmem2[dwidx] <= mid_sample;
	always @(posedge i_clk)
	if (i_reset)
		mid_sample <= 0;
	else if (i_ce)
		mid_sample <= dleft;


	//
	//
	// Calculate the indexes of the filter table
	//
	//

	// Determine if the next clock (not this one) will contain the last
	// valid index, and so whether or not we need to stop.
	wire			last_tap_index, last_data_index;
	wire	[LGNTAPS-2:0]	taps_left;

	assign	taps_left = (QTRTAPS-tidx);
	assign	last_tap_index = (taps_left <= 1);
	assign	last_data_index= (QTRTAPS-tidx <= 2);
	// The pre_acc_ce traveling CE values keep track of when the
	// results of reading memory are valid at the accumulation section
	// of this code later on.
	reg	[3:0]	pre_acc_ce;
	initial	pre_acc_ce = 4'h0;
	always @(posedge i_clk)
	if (i_reset)
		pre_acc_ce[0] <= 1'b0;
	else if (i_ce)
		pre_acc_ce[0] <= 1'b1;
	else if ((pre_acc_ce[0])&&(!last_tap_index))
		pre_acc_ce[0] <= 1'b1;
	else if (!m_ce)
		pre_acc_ce[0] <= 1'b0;
	// pre_acc_ce[0] means the data index is valid
	// pre_acc_ce[1] means the data values are valid, tap index is valid
	// pre_acc_ce[2] means the data sum and tap value are valid
	// pre_acc_ce[3] means that the product is valid

	always @(posedge i_clk)
	if (i_reset)
		pre_acc_ce[3:1] <= 3'b0;
	else
		pre_acc_ce[3:1] <= { pre_acc_ce[2:1],
			((m_ce)||((pre_acc_ce[0])&&(!last_tap_index))) };

	initial	lidx = 0;
	initial	ridx = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		lidx <= 0;
		ridx <= 0;
	end else if (i_ce)
	begin
		lidx <= dwidx; // Newest value
		ridx <= dwidx-(HALFTAPS[LGNMEM-1:0])+1;
	end else if ((m_ce)||(!last_data_index))
	begin
		lidx <= lidx - 2;
		ridx <= ridx + 2;
	end


	initial	tidx = 0;
	always @(posedge i_clk)
	if (i_reset)
		tidx <= 0;
	else if (m_ce)
		tidx <= 0;
	else if (!last_tap_index)
		tidx <= tidx + 1'b1;

	//
	//
	// Read from memory cycle
	//
	//

	//
	// m_ce is the memory strobe.  It is true when the first index is valid
	initial	m_ce = 1'b0;
	always @(posedge i_clk)
		m_ce <= (i_ce)&&(!i_reset);

	initial	dleft  = 0;
	initial	dright = 0;
	always @(posedge i_clk)
	begin
		// dleft  <= dmem1[ didx[LGNMEM-1:0]];
		// dright <= dmem2[~didx[LGNMEM-1:0]];
		dleft  <= dmem1[lidx];
		dright <= dmem2[ridx];
	end

	//
	// Summation cycle, and read coefficient from memory
	//
	// d_ce is valid when the first data from memory is read/valid
	initial	d_ce = 0;
	always @(posedge i_clk)
		d_ce <= (m_ce)&&(!i_reset);

	initial	tap = 0;
	always @(posedge i_clk)
		tap <= tapmem[tidx[(LGNCOEF-1):0]];

	initial	dsum = 0;
	always @(posedge i_clk)
	if (i_reset)
		dsum <= 0;
	else if (OPT_HILBERT)
		dsum   <= dleft - dright;
	else
		dsum   <= dleft + dright;

	// s_ce is valid when the first data sum is valid
	initial	s_ce = 0;
	always @(posedge i_clk)
		s_ce <= (d_ce)&&(!i_reset);

	//
	// Apply the product to the tap and data just read
	//

	initial	product = 0;
	always @(posedge i_clk)
		product <= tap * dsum;

	reg	[OW-1:0]	midprod;
	initial	midprod = 0;
	always @(posedge i_clk)
	if (i_reset)
		midprod <= 0;
	else if (m_ce)
		midprod <= { {(OW-IW-TW+1){mid_sample[IW-1]}},
					mid_sample, {(TW-1){1'b0}}}
				- {{(OW-IW){mid_sample[IW-1]}}, mid_sample};

	initial	r_acc = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_acc <= 0;
	else if (s_ce)
		r_acc <= midprod;
	else if (pre_acc_ce[3])
		r_acc <= r_acc + { {(OW-(IW+TW)){product[(IW+TW-1)]}},
						product };

	//
	//
	// Copy the result to the output
	//
	//
	initial	o_result = 0;
	always @(posedge i_clk)
		if (s_ce)
			o_result <= r_acc;

	initial	o_ce = 1'b0;
	always @(posedge i_clk)
		o_ce <= (s_ce)&&(!i_reset);

endmodule
