////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	slowfil.v
//
// Project:	DSP Filtering Example Project
//
// Purpose:	Unlike fastfir.v and genericfir.v, both of which require one
//		hardware multiply element per tap, this slowfil design requires
//	only one multiply element in total.  It is useful for those times and
//	cases when there are fewer taps than there are clock intervals between
//	incoming samples.  In all other respects, however, it remains quite
//	generic.
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
module	slowfil(i_clk, i_reset, i_tap_wr, i_tap, i_ce, i_sample, o_ce, o_result);
	parameter	LGNTAPS = 7, IW=16, TW=16, OW = IW+TW+LGNTAPS;
	parameter	[LGNTAPS:0]	NTAPS = 110; // (1<<LGNTAPS);
	parameter	[0:0]		FIXED_TAPS = 1'b0;
	parameter			INITIAL_COEFFS  = "";
	localparam	MEMSZ = (1<<LGNTAPS);
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

	reg	[(TW-1):0]	tapmem	[0:(MEMSZ-1)];	// Coef memory
	reg signed [(TW-1):0]	tap;		// Value read from coef memory

	reg	[(LGNTAPS-1):0]	dwidx, didx;	// Data write and read indices
	reg	[(LGNTAPS-1):0]	tidx;		// Coefficient read index
	reg	[(IW-1):0]	dmem	[0:(MEMSZ-1)];	// Data memory
	reg signed [(IW-1):0]	data;		// Data value read from memory

	// Traveling CE values
	reg	d_ce, p_ce, m_ce;
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
	begin
		initial $readmemh(INITIAL_COEFFS, tapmem);

		// Make Verilators -Wall happy
		// Verilator lint_off UNUSED
		wire	[TW:0]	ignored_inputs;
		assign	ignored_inputs = { i_tap_wr, i_tap };
		// Verilator lint_on  UNUSED
	end else begin
		// Coef memory write index
		reg	[(LGNTAPS-1):0]	tapwidx;

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
			dmem[dwidx] <= i_sample;

	//
	//
	// Calculate the indexes of the filter table
	//
	//

	// Determine if the next clock (not this one) will contain the last
	// valid index, and so whether or not we need to stop.
	wire	last_tap_index;
	assign	last_tap_index = (NTAPS[LGNTAPS-1:0]-tidx <= 1);
	// The pre_acc_ce traveling CE values keep track of when the
	// results of reading memory are valid at the accumulation section
	// of this code later on.
	reg	[2:0]	pre_acc_ce;
	initial	pre_acc_ce = 3'h0;
	always @(posedge i_clk)
		if (i_reset)
			pre_acc_ce[0] <= 1'b0;
		else if (i_ce)
			pre_acc_ce[0] <= 1'b1;
		else if ((pre_acc_ce[0])&&(!last_tap_index))
			pre_acc_ce[0] <= 1'b1;
		else
			pre_acc_ce[0] <= 1'b0;
	// pre_acc_ce[0] means that the tap index is valid
	// pre_acc_ce[1] means that the tap value is valid
	// pre_acc_ce[2] means that the product is valid

	always @(posedge i_clk)
		if (i_reset)
			pre_acc_ce[2:1] <= 2'b0;
		else
			pre_acc_ce[2:1] <= pre_acc_ce[1:0];

	initial	didx = 0;
	initial	tidx = 0;
	always @(posedge i_clk)
		if (i_ce)
		begin
			didx <= dwidx;
			tidx <= 0;
		end else begin
			didx <= didx - 1'b1;
			tidx <= tidx + 1'b1;
		end

	// m_ce is valid when the first index is valid
	initial	m_ce = 1'b0;
	always @(posedge i_clk)
		m_ce <= (i_ce)&&(!i_reset);

	//
	//
	// Read from memory cycle
	//
	//
	initial	tap = 0;
	always @(posedge i_clk)
		tap <= tapmem[tidx[(LGNTAPS-1):0]];

	initial	data = 0;
	always @(posedge i_clk)
		data <= dmem[didx];

	// d_ce is valid when the first data from memory is read/valid
	initial	d_ce = 0;
	always @(posedge i_clk)
		d_ce <= (m_ce)&&(!i_reset);

	//
	// Apply the product to the tap and data just read
	//
	// p_ce is valid on the first valid product
	initial	p_ce = 1'b0;
	always @(posedge i_clk)
		p_ce <= (d_ce)&&(!i_reset);

	initial	product = 0;
	always @(posedge i_clk)
		product <= tap * data;

	initial	r_acc = 0;
	always @(posedge i_clk)
		if (p_ce)
			r_acc <={ {(OW-(IW+TW)){product[(IW+TW-1)]}}, product };
		else if (pre_acc_ce[2])
			r_acc <= r_acc + { {(OW-(IW+TW)){product[(IW+TW-1)]}},
						product };

	//
	//
	// Copy the result to the output
	//
	//
	initial	o_result = 0;
	always @(posedge i_clk)
		if (p_ce)
			o_result <= r_acc;

	initial	o_ce = 1'b0;
	always @(posedge i_clk)
		o_ce <= (p_ce)&&(!i_reset);
endmodule
