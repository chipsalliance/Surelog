////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	faxi_master.v (Formal properties of an AXI master)
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	This file contains a set of formal properties which can be
//		used to formally verify that a core truly follows the full
//	AXI4 specification.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017-2019, Gisselquist Technology, LLC
//
// This file is part of the pipelined Wishbone to AXI converter project, a
// project that contains multiple bus bridging designs and formal bus property
// sets.
//
// The bus bridge designs and property sets are free RTL designs: you can
// redistribute them and/or modify any of them under the terms of the GNU
// Lesser General Public License as published by the Free Software Foundation,
// either version 3 of the License, or (at your option) any later version.
//
// The bus bridge designs and property sets are distributed in the hope that
// they will be useful, but WITHOUT ANY WARRANTY; without even the implied
// warranty of MERCHANTIBILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
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
module faxi_master #(
	parameter C_AXI_ID_WIDTH	= 3, // The AXI id width used for R&W
                                             // This is an int between 1-16
	parameter C_AXI_DATA_WIDTH	= 128,// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	= 28,	// AXI Address width (log wordsize)
	localparam DW			= C_AXI_DATA_WIDTH,
	localparam AW			= C_AXI_ADDR_WIDTH,
	parameter [0:0] F_OPT_BURSTS    = 1'b1,	// Check burst lengths
	parameter [7:0] F_AXI_MAXBURST	= 8'hff,// Maximum burst length, minus 1
	parameter 	F_LGDEPTH	= 10,
	parameter 	F_LGFIFO	= 3,
	parameter	[(C_AXI_ID_WIDTH-1):0]	F_AXI_MAXSTALL = 3,
	parameter	[(C_AXI_ID_WIDTH-1):0]	F_AXI_MAXDELAY = 3
	) (
	input	wire			i_clk,	// System clock
	input	wire			i_axi_reset_n,

// AXI write address channel signals
	input	wire			i_axi_awready,//Slave is ready to accept
	input	wire	[C_AXI_ID_WIDTH-1:0]	i_axi_awid,	// Write ID
	input	wire	[AW-1:0]	i_axi_awaddr,	// Write address
	input	wire	[7:0]		i_axi_awlen,	// Write Burst Length
	input	wire	[2:0]		i_axi_awsize,	// Write Burst size
	input	wire	[1:0]		i_axi_awburst,	// Write Burst type
	input	wire	[0:0]		i_axi_awlock,	// Write lock type
	input	wire	[3:0]		i_axi_awcache,	// Write Cache type
	input	wire	[2:0]		i_axi_awprot,	// Write Protection type
	input	wire	[3:0]		i_axi_awqos,	// Write Quality of Svc
	input	wire			i_axi_awvalid,	// Write address valid

// AXI write data channel signals
	input	wire			i_axi_wready,  // Write data ready
	input	wire	[DW-1:0]	i_axi_wdata,	// Write data
	input	wire	[DW/8-1:0]	i_axi_wstrb,	// Write strobes
	input	wire			i_axi_wlast,	// Last write transaction
	input	wire			i_axi_wvalid,	// Write valid

// AXI write response channel signals
	input	wire [C_AXI_ID_WIDTH-1:0] i_axi_bid,	// Response ID
	input	wire	[1:0]		i_axi_bresp,	// Write response
	input	wire			i_axi_bvalid,  // Write reponse valid
	input	wire			i_axi_bready,  // Response ready

// AXI read address channel signals
	input	wire			i_axi_arready,	// Read address ready
	input	wire	[C_AXI_ID_WIDTH-1:0]	i_axi_arid,	// Read ID
	input	wire	[AW-1:0]	i_axi_araddr,	// Read address
	input	wire	[7:0]		i_axi_arlen,	// Read Burst Length
	input	wire	[2:0]		i_axi_arsize,	// Read Burst size
	input	wire	[1:0]		i_axi_arburst,	// Read Burst type
	input	wire	[0:0]		i_axi_arlock,	// Read lock type
	input	wire	[3:0]		i_axi_arcache,	// Read Cache type
	input	wire	[2:0]		i_axi_arprot,	// Read Protection type
	input	wire	[3:0]		i_axi_arqos,	// Read Protection type
	input	wire			i_axi_arvalid,	// Read address valid

// AXI read data channel signals
	input wire [C_AXI_ID_WIDTH-1:0] i_axi_rid,     // Response ID
	input	wire	[1:0]		i_axi_rresp,   // Read response
	input	wire			i_axi_rvalid,  // Read reponse valid
	input	wire	[DW-1:0]	i_axi_rdata,    // Read data
	input	wire			i_axi_rlast,    // Read last
	input	wire			i_axi_rready,  // Read Response ready
	//
	output	reg	[F_LGDEPTH-1:0]		f_axi_rd_nbursts,
	output	reg	[F_LGDEPTH-1:0]		f_axi_rd_outstanding,
	output	reg	[F_LGDEPTH-1:0]		f_axi_wr_nbursts,
	output	reg	[F_LGDEPTH-1:0]		f_axi_awr_outstanding,
	output	reg	[F_LGDEPTH-1:0]		f_axi_awr_nbursts,
		// Address writes without write valids
	//
	// output	reg	[(9-1):0]	f_axi_wr_pending,
	// 
	// RD_COUNT: increment on read w/o last, cleared on read w/ last
	output reg	[C_AXI_ID_WIDTH-1:0]	f_axi_rd_checkid,
	output reg			    	f_axi_rd_ckvalid,
	output reg	[9-1:0]			f_axi_rd_cklen,

	output	reg	[F_LGDEPTH-1:0]		f_axi_rdid_nbursts,
	output	reg	[F_LGDEPTH-1:0]		f_axi_rdid_outstanding,
	output	reg	[F_LGDEPTH-1:0]		f_axi_rdid_ckign_nbursts,
	output	reg	[F_LGDEPTH-1:0]		f_axi_rdid_ckign_outstanding
);

//*****************************************************************************
// Parameter declarations
//*****************************************************************************

	localparam	LG_AXI_DW	= ( C_AXI_DATA_WIDTH ==   8) ? 3
					: ((C_AXI_DATA_WIDTH ==  16) ? 4
					: ((C_AXI_DATA_WIDTH ==  32) ? 5
					: ((C_AXI_DATA_WIDTH ==  64) ? 6
					: ((C_AXI_DATA_WIDTH == 128) ? 7
					: 8))));

	localparam	LG_WB_DW	= ( DW ==   8) ? 3
					: ((DW ==  16) ? 4
					: ((DW ==  32) ? 5
					: ((DW ==  64) ? 6
					: ((DW == 128) ? 7
					: 8))));
	localparam	LGFIFOLN = C_AXI_ID_WIDTH;
	localparam	FIFOLN = (1<<LGFIFOLN);
	localparam	F_LGDEPTH = C_AXI_ID_WIDTH;
	localparam	F_AXI_MAXWAIT = F_AXI_MAXSTALL;


//*****************************************************************************
// Internal register and wire declarations
//*****************************************************************************


	// wire	w_fifo_full;
	wire	axi_rd_ack, axi_wr_ack, axi_ard_req, axi_awr_req, axi_wr_req,
		axi_rd_err, axi_wr_err;
	//
	assign	axi_ard_req = (i_axi_arvalid)&&(i_axi_arready);
	assign	axi_awr_req = (i_axi_awvalid)&&(i_axi_awready);
	assign	axi_wr_req  = (i_axi_wvalid )&&(i_axi_wready);
	//
	assign	axi_rd_ack = (i_axi_rvalid)&&(i_axi_rready);
	assign	axi_wr_ack = (i_axi_bvalid)&&(i_axi_bready);
	assign	axi_rd_err = (axi_rd_ack)&&(i_axi_rresp[1]);
	assign	axi_wr_err = (axi_wr_ack)&&(i_axi_bresp[1]);

`define	SLAVE_ASSUME	assert
`define	SLAVE_ASSERT	assume

	//
	// Setup
	//
	reg	f_past_valid;
	integer	k;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;
	always @(*)
	if (!f_past_valid)
		assert(!i_axi_reset_n);

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Reset properties
	//
	//
	////////////////////////////////////////////////////////////////////////
	localparam [0:0]	F_OPT_ASSUME_RESET = 1'b1;
	generate if (F_OPT_ASSUME_RESET)
	begin : ASSUME_INITIAL_RESET
		always @(*)
		if (!f_past_valid)
			assume(!i_axi_reset_n);
	end else begin : ASSERT_INITIAL_RESET
		always @(*)
		if (!f_past_valid)
			assert(!i_axi_reset_n);
	end endgenerate
	//
	// If asserted, the reset must be asserted for a minimum of 16 clocks
	reg	[3:0]	f_reset_length;
	initial	f_reset_length = 0;
	always @(posedge i_clk)
	if (i_axi_reset_n)
		f_reset_length <= 0;
	else if (!(&f_reset_length))
		f_reset_length <= f_reset_length + 1'b1;

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_axi_reset_n))&&(!$past(&f_reset_length)))
		`SLAVE_ASSUME(!i_axi_reset_n);

	generate if (F_OPT_ASSUME_RESET)
	begin : ASSUME_RESET
		always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_axi_reset_n))&&(!$past(&f_reset_length)))
			assume(!i_axi_reset_n);

		always @(*)
		if ((f_reset_length > 0)&&(f_reset_length < 4'hf))
			assume(!i_axi_reset_n);

	end else begin : ASSERT_RESET

		always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_axi_reset_n))&&(!$past(&f_reset_length)))
			assert(!i_axi_reset_n);

		always @(*)
		if ((f_reset_length > 0)&&(f_reset_length < 4'hf))
			assert(!i_axi_reset_n);

	end endgenerate

	always @(posedge i_clk)
	if ((!f_past_valid)||(!$past(i_axi_reset_n)))
	begin
		`SLAVE_ASSUME(!i_axi_arvalid);
		`SLAVE_ASSUME(!i_axi_awvalid);
		`SLAVE_ASSUME(!i_axi_wvalid);
		//
		`SLAVE_ASSERT(!i_axi_bvalid);
		`SLAVE_ASSERT(!i_axi_rvalid);
	end

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Stability properties--what happens if valid and not ready
	//
	//
	////////////////////////////////////////////////////////////////////////

	// Assume any response from the bus will not change prior to that
	// response being accepted
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_axi_reset_n)))
	begin
		// Write address channel
		if ((f_past_valid)&&($past(i_axi_awvalid))&&(!$past(i_axi_awready)))
		begin
			`SLAVE_ASSUME(i_axi_awvalid);
			`SLAVE_ASSUME($stable(i_axi_awaddr));
			// `SLAVE_ASSUME($stable(i_axi_awid));
			`SLAVE_ASSUME($stable(i_axi_awlen));
			`SLAVE_ASSUME($stable(i_axi_awsize));
			`SLAVE_ASSUME($stable(i_axi_awburst));
			`SLAVE_ASSUME($stable(i_axi_awlock));
			`SLAVE_ASSUME($stable(i_axi_awcache));
			`SLAVE_ASSUME($stable(i_axi_awprot));
			`SLAVE_ASSUME($stable(i_axi_awqos));
		end

		// Write data channel
		if ((f_past_valid)&&($past(i_axi_wvalid))&&(!$past(i_axi_wready)))
		begin
			`SLAVE_ASSUME(i_axi_wvalid);
			`SLAVE_ASSUME($stable(i_axi_wstrb));
			`SLAVE_ASSUME($stable(i_axi_wdata));
			`SLAVE_ASSUME($stable(i_axi_wlast));
		end

		// Incoming Read address channel
		if ((f_past_valid)&&($past(i_axi_arvalid))&&(!$past(i_axi_arready)))
		begin
			`SLAVE_ASSUME(i_axi_arvalid);
			// `SLAVE_ASSUME($stable(i_axi_arid));
			`SLAVE_ASSUME($stable(i_axi_araddr));
			`SLAVE_ASSUME($stable(i_axi_arlen));
			`SLAVE_ASSUME($stable(i_axi_arsize));
			`SLAVE_ASSUME($stable(i_axi_arburst));
			`SLAVE_ASSUME($stable(i_axi_arlock));
			`SLAVE_ASSUME($stable(i_axi_arcache));
			`SLAVE_ASSUME($stable(i_axi_arprot));
			`SLAVE_ASSUME($stable(i_axi_arqos));
		end

		// Assume any response from the bus will not change prior to that
		// response being accepted
		if ((f_past_valid)&&($past(i_axi_rvalid))&&(!$past(i_axi_rready)))
		begin
			`SLAVE_ASSERT(i_axi_rvalid);
			// `SLAVE_ASSERT($stable(i_axi_rid));
			`SLAVE_ASSERT($stable(i_axi_rresp));
			`SLAVE_ASSERT($stable(i_axi_rdata));
			`SLAVE_ASSERT($stable(i_axi_rlast));
		end

		if ((f_past_valid)&&($past(i_axi_bvalid))&&(!$past(i_axi_bready)))
		begin
			`SLAVE_ASSERT(i_axi_bvalid);
			`SLAVE_ASSERT($stable(i_axi_bid));
			`SLAVE_ASSERT($stable(i_axi_bresp));
		end
	end

	// Nothing should be returned or requested on the first clock
	initial	`SLAVE_ASSUME(!i_axi_arvalid);
	initial	`SLAVE_ASSUME(!i_axi_awvalid);
	initial	`SLAVE_ASSUME(!i_axi_wvalid);
	//
	initial	`SLAVE_ASSERT(!i_axi_bvalid);
	initial	`SLAVE_ASSERT(!i_axi_rvalid);

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Insist upon a maximum delay before a request is accepted
	//
	//
	////////////////////////////////////////////////////////////////////////

	generate if (F_AXI_MAXWAIT > 0)
	begin : CHECK_STALL_COUNT
		//
		// AXI write address channel
		//
		//
		reg	[(F_LGDEPTH-1):0]	f_axi_awstall,
						f_axi_wstall,
						f_axi_arstall,
						f_axi_bstall,
						f_axi_rstall;

		initial	f_axi_awstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_awvalid)||(i_axi_awready))
			f_axi_awstall <= 0;
		else if ((!i_axi_bvalid)||(i_axi_bready))
			f_axi_awstall <= f_axi_awstall + 1'b1;

		always @(*)
			`SLAVE_ASSERT(f_axi_awstall < F_AXI_MAXWAIT);

		//
		// AXI write data channel
		//
		//
		// AXI explicitly allows write bursts with zero strobes.  This is part
		// of how a transaction is aborted (if at all).

		initial	f_axi_wstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_wvalid)||(i_axi_wready)
				||(i_axi_bvalid))
			f_axi_wstall <= 0;
		else if ((!i_axi_bvalid)||(i_axi_bready))
			f_axi_wstall <= f_axi_wstall + 1'b1;

		always @(*)
			`SLAVE_ASSERT(f_axi_wstall < F_AXI_MAXWAIT);

		//
		// AXI read address channel
		//
		//
		initial	f_axi_arstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_arvalid)||(i_axi_arready)
				||(i_axi_rvalid))
			f_axi_arstall <= 0;
		else if ((!i_axi_rvalid)||(i_axi_rready))
			f_axi_arstall <= f_axi_arstall + 1'b1;

		always @(*)
			`SLAVE_ASSERT(f_axi_arstall < F_AXI_MAXWAIT);

		// AXI write response channel
		initial	f_axi_bstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_bvalid)||(i_axi_bready))
			f_axi_bstall <= 0;
		else
			f_axi_bstall <= f_axi_bstall + 1'b1;

		always @(*)
			`SLAVE_ASSUME(f_axi_bstall < F_AXI_MAXWAIT);

		// AXI read response channel
		initial	f_axi_rstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_rvalid)||(i_axi_rready))
			f_axi_rstall <= 0;
		else
			f_axi_rstall <= f_axi_rstall + 1'b1;

		always @(*)
			`SLAVE_ASSUME(f_axi_rstall < F_AXI_MAXWAIT);

	end endgenerate


	////////////////////////////////////////////////////////////////////////
	//
	//
	// Count outstanding transactions.  With these measures, we count
	// once per any burst.
	//
	//
	////////////////////////////////////////////////////////////////////////
	initial	f_axi_awr_outstanding = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_awr_outstanding <= 0;
	else case({ (axi_awr_req), (axi_wr_req) })
		2'b10: f_axi_awr_outstanding <= f_axi_awr_outstanding + i_axi_awlen+1;
		2'b01: f_axi_awr_outstanding <= f_axi_awr_outstanding - 1'b1;
		2'b11: f_axi_awr_outstanding <= f_axi_awr_outstanding + i_axi_awlen; // +1 -1
		default: begin end
	endcase

	initial	f_axi_awr_nbursts = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_awr_nbursts <= 0;
	else case({ (axi_awr_req), (axi_wr_ack) })
	2'b10: f_axi_awr_nbursts <= f_axi_awr_nbursts + 1'b1;
	2'b01: f_axi_awr_nbursts <= f_axi_awr_nbursts - 1'b1;
	default: begin end
	endcase

	initial	f_axi_wr_nbursts = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_wr_nbursts <= 0;
	else case({ (axi_wr_req)&&(i_axi_wlast), (axi_wr_ack) })
	2'b01: f_axi_wr_nbursts <= f_axi_wr_nbursts - 1'b1;
	2'b10: f_axi_wr_nbursts <= f_axi_wr_nbursts + 1'b1;
	default: begin end
	endcase

	initial	f_axi_rd_nbursts = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_rd_nbursts <= 0;
	else case({ (axi_ard_req), (axi_rd_ack)&&(i_axi_rlast) })
	2'b01: f_axi_rd_nbursts <= f_axi_rd_nbursts - 1'b1;
	2'b10: f_axi_rd_nbursts <= f_axi_rd_nbursts + 1'b1;
	endcase

	initial	f_axi_rd_outstanding = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_rd_outstanding <= 0;
	else case({ (axi_ard_req), (axi_rd_ack) })
	2'b01: f_axi_rd_outstanding <= f_axi_rd_outstanding - 1'b1;
	2'b10: f_axi_rd_outstanding <= f_axi_rd_outstanding + i_axi_arlen+1;
	2'b11: f_axi_rd_outstanding <= f_axi_rd_outstanding + i_axi_arlen;
	endcase

	// Do not let the number of outstanding requests overflow
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_awr_outstanding < {(F_LGDEPTH){1'b1}});
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_rd_outstanding  < {(F_LGDEPTH){1'b1}});
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_awr_nbursts < {(F_LGDEPTH){1'b1}});
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_wr_nbursts  < {(F_LGDEPTH){1'b1}});
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_rd_nbursts  < {(F_LGDEPTH){1'b1}});

	// Cannot have outstanding values if there aren't any outstanding
	// bursts
	always @(posedge i_clk)
	if (f_axi_awr_outstanding > 0)
		`SLAVE_ASSERT(f_axi_awr_nbursts > 0);
	// else if (f_axi_awr_outstanding == 0)
	//	Doesn't apply.  Might have awr_outstanding == 0 and
	//	awr_nbursts>0
	always @(posedge i_clk)
	if (f_axi_rd_outstanding > 0)
		`SLAVE_ASSERT(f_axi_rd_nbursts > 0);
	else
		`SLAVE_ASSERT(f_axi_rd_nbursts == 0);
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_rd_nbursts <= f_axi_rd_outstanding);

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Insist that all responses are returned in less than a maximum delay
	// In this case, we count responses within a burst, rather than entire
	// bursts.
	//
	//
	////////////////////////////////////////////////////////////////////////

	generate if (F_AXI_MAXDELAY > 0)
	begin : CHECK_MAX_DELAY

		reg	[(F_LGDEPTH-1):0]	f_axi_wr_ack_delay,
						f_axi_awr_ack_delay,
						f_axi_rd_ack_delay;

		initial	f_axi_rd_ack_delay = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(i_axi_rvalid)||(f_axi_rd_outstanding==0))
			f_axi_rd_ack_delay <= 0;
		else
			f_axi_rd_ack_delay <= f_axi_rd_ack_delay + 1'b1;

		initial	f_axi_wr_ack_delay = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||((i_axi_wvalid)&&(!i_axi_wlast))
				||(i_axi_bvalid)||(f_axi_awr_outstanding==0))
			f_axi_wr_ack_delay <= 0;
		else
			f_axi_wr_ack_delay <= f_axi_wr_ack_delay + 1'b1;

		initial	f_axi_awr_ack_delay = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(i_axi_bvalid)||(i_axi_wvalid)
					||(f_axi_awr_nbursts == 0)
					||(f_axi_wr_nbursts == 0))
			f_axi_awr_ack_delay <= 0;
		else
			f_axi_awr_ack_delay <= f_axi_awr_ack_delay + 1'b1;

		always @(*)
			`SLAVE_ASSERT(f_axi_rd_ack_delay < F_AXI_MAXDELAY);

		always @(*)
			`SLAVE_ASSERT(f_axi_wr_ack_delay < F_AXI_MAXDELAY);

		always @(posedge i_clk)
			`SLAVE_ASSERT(f_axi_awr_ack_delay < F_AXI_MAXDELAY);
	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Assume acknowledgements must follow requests
	//
	// The outstanding count is a count of bursts, but the acknowledgements
	// we are looking for are individual.  Hence, there should be no
	// individual acknowledgements coming back if there's no outstanding
	// burst.
	//
	//
	////////////////////////////////////////////////////////////////////////

	//
	// AXI write response channel
	//
	always @(posedge i_clk)
	if (i_axi_bvalid)
	begin
		`SLAVE_ASSERT(f_axi_awr_nbursts > 0);
		`SLAVE_ASSERT(f_axi_wr_nbursts > 0);
	end

	//
	// AXI read data channel signals
	//
	always @(posedge i_clk)
	if (i_axi_rvalid)
	begin
		`SLAVE_ASSERT(f_axi_rd_outstanding > 0);
		`SLAVE_ASSERT(f_axi_rd_nbursts > 0);
		if (!i_axi_rlast)
			`SLAVE_ASSERT(f_axi_rd_outstanding > 1);
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Xilinx extensions
	//
	////////////////////////////////////////////////////////////////////////
	always @(posedge i_clk)
	if (f_axi_wr_nbursts > 0)
		`SLAVE_ASSUME(i_axi_wvalid);

	////////////////////////////////////////////////////////////////////////
	//
	//
	//
	////////////////////////////////////////////////////////////////////////

	generate if (!F_OPT_BURSTS)
	begin

		always @(posedge i_clk)
		if (i_axi_awvalid)
			`SLAVE_ASSUME(i_axi_awlen == 0);

		always @(posedge i_clk)
		if (i_axi_wvalid)
			`SLAVE_ASSUME(i_axi_wlast);

		always @(posedge i_clk)
		if (i_axi_arvalid)
			`SLAVE_ASSUME(i_axi_arlen == 0);

		always @(*)
		if (i_axi_rvalid)
			`SLAVE_ASSERT(i_axi_rlast);

		always @(*)
			`SLAVE_ASSERT(f_axi_rd_nbursts == f_axi_rd_outstanding);
	end endgenerate



	////////////////////////////////////////////////////////////////////////
	//
	// Read Burst counting
	//
	(* anyseq *)	reg				f_axi_rd_check;
	(* anyconst *)	reg	[C_AXI_ID_WIDTH-1:0]	r_axi_rd_checkid;
	always @(*)
		f_axi_rd_checkid = r_axi_rd_checkid;

	initial	f_axi_rdid_nbursts = 0;
	initial	f_axi_rdid_outstanding = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
	begin
		f_axi_rdid_nbursts <= 0;
		f_axi_rdid_outstanding <= 0;
	end else case({	(i_axi_arvalid&& i_axi_arready&&
				(i_axi_arid == f_axi_rd_checkid)),
			(i_axi_rvalid && i_axi_rready &&
				(i_axi_rid == f_axi_rd_checkid)) })
	2'b01: begin
		if (i_axi_rlast)
			f_axi_rdid_nbursts <= f_axi_rdid_nbursts - 1;
		f_axi_rdid_outstanding <= f_axi_rdid_outstanding - 1;
		end
	2'b10: begin
		f_axi_rdid_nbursts <= f_axi_rdid_nbursts + 1;
		f_axi_rdid_outstanding <= f_axi_rdid_outstanding+i_axi_arlen+ 1;
		end
	2'b11: begin
		if (!i_axi_rlast)
			f_axi_rdid_nbursts <= f_axi_rdid_nbursts + 1;
		f_axi_rdid_outstanding <= f_axi_rdid_outstanding + i_axi_arlen;
		end
	default: begin end
	endcase

	initial	f_axi_rdid_ckign_nbursts = 0;
	initial	f_axi_rdid_ckign_outstanding = 0;
	initial	f_axi_rd_ckvalid = 0;
	initial	f_axi_rd_cklen = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
	begin
		f_axi_rdid_ckign_nbursts <= 0;
		f_axi_rdid_ckign_outstanding <= 0;
		f_axi_rd_ckvalid <= 0;
		f_axi_rd_cklen <= 0;
	end else begin

		if (!f_axi_rd_ckvalid && f_axi_rd_check && i_axi_arid == f_axi_rd_checkid
			&& i_axi_arvalid && i_axi_arready)
		begin
			f_axi_rd_ckvalid <= 1'b1;
			f_axi_rdid_ckign_nbursts <= f_axi_rdid_nbursts
			  - ((i_axi_rvalid && i_axi_rready
				&& i_axi_rid == f_axi_rd_checkid
				&& i_axi_rlast) ? 1:0);
			f_axi_rdid_ckign_outstanding <= f_axi_rdid_outstanding
			  - ((i_axi_rvalid && i_axi_rready
				&& i_axi_rid == f_axi_rd_checkid) ? 1:0);
			f_axi_rd_cklen <= i_axi_arlen + 1;
		end else if (f_axi_rd_ckvalid && i_axi_rvalid && i_axi_rready
					&& i_axi_rid == f_axi_rd_checkid)
		begin
			if (f_axi_rdid_ckign_nbursts > 0)
			begin
				if (i_axi_rlast)
					f_axi_rdid_ckign_nbursts <= f_axi_rdid_ckign_nbursts-1;
				f_axi_rdid_ckign_outstanding <= f_axi_rdid_ckign_outstanding-1;
			end else begin
				`SLAVE_ASSERT(i_axi_rlast == (f_axi_rd_cklen == 1));
				f_axi_rd_cklen <= f_axi_rd_cklen - 1;
				if (i_axi_rlast)
					f_axi_rd_ckvalid <= 1'b0;
			end
		end
	end

	always @(*)
		assert(f_axi_rdid_outstanding <= f_axi_rd_outstanding);
	always @(*)
		assert(f_axi_rdid_nbursts <= f_axi_rd_nbursts);
	always @(*)
	if (f_axi_rd_ckvalid)
		assert(f_axi_rdid_ckign_nbursts <= f_axi_rdid_nbursts);
	always @(*)
	if (f_axi_rd_ckvalid)
		assert(f_axi_rdid_ckign_outstanding <= f_axi_rdid_outstanding);
	always @(*)
	if (!f_axi_rd_ckvalid)
	begin
		assert(f_axi_rd_cklen == 0);
		assert(f_axi_rdid_ckign_nbursts == 0);
		assert(f_axi_rdid_ckign_outstanding == 0);
	end
endmodule
