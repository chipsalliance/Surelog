////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	boxcar.v
//
// Project:	DSP Filtering Example Project
//
// Purpose:	This filter expands upon the capabilities of the simplest.v
//		non-trivial filter.  Like simplest.v, this filter only averages
//	samples together.  Unlike the simplest.v filter, this filter will
//	average more than two samples together.  Indeed, the number of samples
//	that can be averaged together is programmable from 1 to
//	(1<<LGMEM)-1.  To change the number of averages, raise the reset signal,
//	i_reset, and set i_navg while i_reset is set.  Upon clearing i_reset,
//	the right number of taps will be set.
//
// Algorithm:
//
//	y[n] = SUM_{k=0}^{navg-1} x[n-k]
//		= y[n-1] + x[n] - x[n-navg]
//
//	We'll use block RAM to hold the x[n-navg] value.
//
// Pipeline scheduling: The following variables are set on the given pipeline
// 		stages:
//
//	(PRE)	navg (set on reset)
//
//	0	rdaddr
//	1	mem[rdaddr]
//	2	memval
//		ival
//		full
//		wraddr
//	3	sub
//		mem[wraddr]
//	4	acc
//	5	rounded, and thence o_result
//
// The overall delay of this algorithm is four samples.  One to clock in
// the input, and three more to get to where the input has an effect.
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
module	boxcar(i_clk, i_reset, i_navg, i_ce, i_sample, o_result);
	parameter	IW=16,		// Input bit-width
			LGMEM=6,	// Size of the memory.
			OW=(IW+LGMEM);	// Output bit-width
	parameter [0:0]	FIXED_NAVG=1'b0; // True if number of averages is fixed
	parameter [0:0]	OPT_SIGNED=1'b1; // True for averaging signed numbers
	// Always assume we'll be averaging by the maximum amount, unless told
	// otherwise.  Minus one, in two's complement, will become this number
	// when interpreted as an unsigned number.
	parameter	[(LGMEM-1):0]	INITIAL_NAVG= -1; // Initial avglen
	input	wire			i_clk,	// Data clock
					i_reset;// Positive synchronous reset
	input	wire	[(LGMEM-1):0]	i_navg;	// Requested number of averages
	//
	input	wire			i_ce;	// True if i_sample is valid
	input	wire	[(IW-1):0]	i_sample;// Input value to be filtered
	output	reg	[(OW-1):0]	o_result;// Output filter value

	reg			full;
	reg	[(LGMEM-1):0]	rdaddr, wraddr;
	reg	[(IW-1):0]	mem [0:((1<<LGMEM)-1)];
	reg	[(IW-1):0]	preval, memval;
	reg	[IW:0]	sub;
	reg	[(IW+LGMEM-1):0] acc;

	// The write address.  We'll write into our memory using this address.
	// It starts at zero, and increments on every valid sample.
	initial	wraddr = 0;
	always @(posedge i_clk)
	if (i_reset)
		wraddr <= 0;
	else if (i_ce)
		wraddr <= wraddr + 1'b1;

	// Calculate the requested number of averages.  If this value is
	// fixed, these will be INITIAL_NAVG and the input i_navg will be
	// ignored, else the requested number will be the number given on
	// the input.
	wire	[(LGMEM-1):0]	w_requested_navg;
	assign w_requested_navg = (FIXED_NAVG) ? INITIAL_NAVG : i_navg;

	// The read address.  We'll keep a running sum of values, and then need
	// to subtract the value dropping off of the end of the summation. 
	// We'll get this value from memory, using our read address to get
	// there.
	//
	// One trick in this code is that we don't want to waste the logic to
	// to initialize memory.  For this reason, we'll declare all memory
	// values to be zero on reset, and only start using the memory once
	// all values have been set.
	initial	rdaddr = -INITIAL_NAVG;
	always @(posedge i_clk)
	if (i_reset)
		rdaddr <= -w_requested_navg;
	else if (i_ce)
		// rdaddr <= wraddr - navg + 1'b1;
		rdaddr <= rdaddr + 1'b1;

	//
	// Clock stage one
	//
	//
	// "preval" just moves things down one stage in time, to give us
	// a clock to read from our memory
	initial	preval = 0;
	always @(posedge i_clk)
	if (i_reset)
		preval <= 0;
	else if (i_ce)
		preval <= i_sample;

	always @(posedge i_clk)
	if (i_ce)
		mem[wraddr] <= i_sample;

	initial	memval = 0;
	always @(posedge i_clk)
	if (i_ce)
		memval <= mem[rdaddr];

	initial	full   = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		full <= 0;
	else if (i_ce)
		full <= (full)||(rdaddr==0);

	// Clock stage two
	//
	// This stage uses the results of stage one.  Note the sign extension
	// below.  (One of my simulators required me to do that ...)
	//
	initial	sub = 0;
	always @(posedge i_clk)
	if (i_reset)
		sub <= 0;
	else if (i_ce)
	begin
		if (full)
			sub <= { OPT_SIGNED&preval[(IW-1)], preval }
					- { OPT_SIGNED&memval[(IW-1)], memval };
		else
			sub <= { OPT_SIGNED&preval[(IW-1)], preval };
	end

	// Clock stage three
	//
	// Using the difference from stage two, calculate the overall block
	// average summation.
	initial	acc = 0;
	always @(posedge i_clk)
	if (i_reset)
		acc <= 0;
	else if (i_ce)
		acc <= acc + { {(LGMEM-1){OPT_SIGNED&sub[IW]}}, sub };

	//
	// Clock stage four
	//
	//
	// Round the result from IW+LGMEM bits down to OW bits.  Also, deal
	// with all the various cases of relationships between IW+LGLEN and OW
	wire	[(IW+LGMEM-1):0]	rounded;
	generate
	// if (IW+LGMEM < OW)
		// CANNOT BE: rounded is only IW+LGLEN bits long
		// Besides, artificially increasing the number of bits doesn't
		// really make sense
	if (IW+LGMEM == OW)
		// No rounding required, output is the acc(umulator)
		assign	rounded = acc;
	else if (IW+LGMEM == OW + 1)
		// Need to drop one bit, round towards even
		assign	rounded = acc + { {(OW){1'b0}}, acc[1] };
	else // if (IW+LGMEM > OW)
		// Drop more than one bit, rounding towards even
		assign	rounded = acc + {
				{(OW){1'b0}},
				acc[(IW+LGMEM-OW)],
				{(IW+LGMEM-OW-1){!acc[(IW+LGMEM-OW)]}}
				};
	endgenerate

	// (Still stage four)
	// rounded is set with combinatorial logic.  It's also set to
	// IW+LGMEM bits.  So, let's take a clock and drop from IW+LGMEM bits
	// to however many bits have been requested of us.
	initial	o_result = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_result <= 0;
	else if (i_ce)
		o_result <= rounded[(IW+LGMEM-1):(IW+LGMEM-OW)];

`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	reg	[(LGMEM-1):0]	f_navg;

	always @(*)
	if ((!FIXED_NAVG)&&(!f_past_valid))
		assume(i_reset);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_ce)))
		assume(i_ce);

	always @(*)
	if ((!FIXED_NAVG)&&(i_reset))
		assume(i_navg > 3);

	always @(posedge i_clk)
	if ((f_test[3])&&(f_navg < (1<<LGMEM)-3))
		assert(f_sum == acc);

	always @(*)
		assert(f_navg > 3);

	always @(posedge i_clk)
		cover($rose(full));

	initial	f_navg = INITIAL_NAVG;
	always @(posedge i_clk)
	if (FIXED_NAVG)
		f_navg <= INITIAL_NAVG;
	else if (i_reset)
		f_navg <= i_navg;


	wire	[LGMEM-1:0]	f_rdaddr;
	assign	f_rdaddr = wraddr - f_navg;
	always @(posedge i_clk)
	if (!i_reset)
		assert(f_rdaddr == rdaddr);

	integer	k;
	reg	[LGMEM+IW-1:0]	f_sum;
	always @(*)
	begin
		f_sum = 0;
		for(k=0; k<(1<<LGMEM); k=k+1)
		begin
			if (((full)&&(k<f_navg)) || ((!full)&&(wraddr>=3)&&(k < wraddr-2)))
				f_sum = f_sum
				+ {{(LGMEM){OPT_SIGNED&mem[wraddr-k-3][IW-1]}},
				    mem[wraddr-k-3] };
		end
	end

	wire	[LGMEM-1:0]	f_full_addr;
	assign	f_full_addr = - f_navg;

	always @(*)
	if ((rdaddr < f_full_addr)&&(rdaddr != 0))
		assert(full);

	reg	[3:0]	f_test;
	initial	f_test = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_test <= 0;
	else if ((full)&&(i_ce))
		f_test <= { f_test[2:0], 1'b1 };

	always @(posedge i_clk)
	if ((f_test[3])&&(f_navg < (1<<LGMEM)-4))
		assert(f_sum == acc);
	else if ((wraddr > 1)&&(!full))
		assert(f_sum == acc);
`endif
endmodule
