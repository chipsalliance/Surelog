////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	dspswitch.v
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
`default_nettype none
module	dspswitch(i_clk, i_areset_n, i_en, i_ce, i_sample, i_bypass,
		o_ce, o_sample);
	parameter	DW = 32;
	input	wire			i_clk, i_areset_n, i_en;
	//
	input	wire			i_ce;
	input	wire	[(DW-1):0]	i_sample, i_bypass;
	//
	output	reg			o_ce;
	output	reg	[(DW-1):0]	o_sample;
	
	initial	o_ce = 0;
	always @(posedge i_clk, negedge i_areset_n)
		if (!i_areset_n)
			o_ce <= 0;
		else
			o_ce <= i_ce;

	initial	o_sample = 0;
	always @(posedge i_clk, negedge i_areset_n)
		if (!i_areset_n)
			o_sample <= 0;
		else if (i_ce)
			o_sample <= (i_en) ? i_sample : i_bypass;

endmodule
