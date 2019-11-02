// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    All Rights Reserved Worldwide
// 
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//


module dual_eth
(
  // WISHBONE common
  wb_clk_i, wb_rst_i,

  // WISHBONE slave
  wb_adr_i, wb_sel_i, wb_we_i,
  wb_dat_i, wb_dat_o, wb_cyc_i,
  wb_stb_i, wb_ack_o, wb_err_o, 

  // WISHBONE master
  m_wb_adr_o, m_wb_sel_o, m_wb_we_o, 
  m_wb_dat_o, m_wb_dat_i, m_wb_cyc_o, 
  m_wb_stb_o, m_wb_ack_i, m_wb_err_i, 

  //TX
  m0tx_clk_pad_i, m0txd_pad_o, m0txen_pad_o, m0txerr_pad_o,
  m1tx_clk_pad_i, m1txd_pad_o, m1txen_pad_o, m1txerr_pad_o,

  //RX
  m0rx_clk_pad_i, m0rxd_pad_i, m0rxdv_pad_i, m0rxerr_pad_i,
  m1rx_clk_pad_i, m1rxd_pad_i, m1rxdv_pad_i, m1rxerr_pad_i,

  m0coll_pad_i, m0crs_pad_i, 
  m1coll_pad_i, m1crs_pad_i, 
  
  int0, int1
);


// WISHBONE common
input           wb_clk_i;     // WISHBONE clock
input           wb_rst_i;     // WISHBONE reset

// WISHBONE slave
input   [31:2]  wb_adr_i;     // WISHBONE address input
input    [3:0]  wb_sel_i;     // WISHBONE byte select input
input           wb_we_i;      // WISHBONE write enable input
input   [31:0]  wb_dat_i;     // WISHBONE data input
output  [31:0]  wb_dat_o;     // WISHBONE data output
output          wb_err_o;     // WISHBONE error output
input           wb_cyc_i;     // WISHBONE cycle input
input           wb_stb_i;     // WISHBONE strobe input
output          wb_ack_o;     // WISHBONE acknowledge output

// WISHBONE master
output  [31:0]  m_wb_adr_o;
output   [3:0]  m_wb_sel_o;
output          m_wb_we_o;
input   [31:0]  m_wb_dat_i;
output  [31:0]  m_wb_dat_o;
output          m_wb_cyc_o;
output          m_wb_stb_o;
input           m_wb_ack_i;
input           m_wb_err_i;

// Tx
input           m0tx_clk_pad_i; // Transmit clock (from PHY)
output   [3:0]  m0txd_pad_o;    // Transmit nibble (to PHY)
output          m0txen_pad_o;   // Transmit enable (to PHY)
output          m0txerr_pad_o;  // Transmit error (to PHY)

input           m1tx_clk_pad_i; // Transmit clock (from PHY)
output   [3:0]  m1txd_pad_o;    // Transmit nibble (to PHY)
output          m1txen_pad_o;   // Transmit enable (to PHY)
output          m1txerr_pad_o;  // Transmit error (to PHY)

// Rx
input           m0rx_clk_pad_i; // Receive clock (from PHY)
input    [3:0]  m0rxd_pad_i;    // Receive nibble (from PHY)
input           m0rxdv_pad_i;   // Receive data valid (from PHY)
input           m0rxerr_pad_i;  // Receive data error (from PHY)

input           m1rx_clk_pad_i; // Receive clock (from PHY)
input    [3:0]  m1rxd_pad_i;    // Receive nibble (from PHY)
input           m1rxdv_pad_i;   // Receive data valid (from PHY)
input           m1rxerr_pad_i;  // Receive data error (from PHY)

// Common Tx and Rx
input           m0coll_pad_i;   // Collision (from PHY)
input           m0crs_pad_i;    // Carrier sense (from PHY)

input           m1coll_pad_i;   // Collision (from PHY)
input           m1crs_pad_i;    // Carrier sense (from PHY)

output          int0, int1;     // Interrupt output


//
// WB Slave Decoder
//
wire          wb_sel_0, wb_sel_1;
wire  [31:0]  wb_dat_0, wb_dat_1;
wire          wb_err_0, wb_err_1;
wire          wb_ack_0, wb_ack_1;
wire          int0, int1;

wire    slv_0 = (wb_adr_i[31:16] === 16'h0000);
wire    slv_1 = (wb_adr_i[31:16] === 16'h0001);

assign  wb_ack_o = (slv_0) ? wb_ack_0 : wb_ack_1;
assign  wb_err_o = (slv_0) ? wb_err_0 : wb_err_1;
assign  wb_dat_o = (slv_0) ? wb_dat_0 : wb_dat_1;

assign  wb_cyc_0 = slv_0 & wb_cyc_i;
assign  wb_cyc_1 = slv_1 & wb_cyc_i;


//
// WB Master arbiter
//
wire [1:0] m_wb_cyc;
reg  [1:0] mst_gt;
reg        last_gt;
always @ (posedge wb_clk_i)
begin
   mst_gt  <= 2'b00;
   if (wb_rst_i) last_gt <= 0;
   else if (m_wb_cyc) begin : mst_arb
      reg gt;

      casex ({m_wb_cyc[0], mst_gt[0], m_wb_cyc[1], mst_gt[1]})
       4'b1x0x: gt = 0;           // Only 0 is requesting
       4'b0x1x: gt = 1;           // Only 1 is requesting
       4'b11xx: gt = 0;           // 0 is parked
       4'bxx11: gt = 0;           // 1 is parked
       4'b1010: gt = last_gt + 1; // Concurrent new requet
      endcase
      
      mst_gt[gt]   <= 1'b1;
      last_gt      <= gt;
   end
end

wire  [31:0]  m_wb_adr_0, m_wb_adr_1;
assign m_wb_adr_o = (mst_gt[0]) ? m_wb_adr_0 : m_wb_adr_1;

wire   [3:0]  m_wb_sel_0, m_wb_sel_1;
assign m_wb_sel_o = (mst_gt[0]) ? m_wb_sel_0 : m_wb_sel_1;

wire          m_wb_we_0, m_wb_we_1;
assign m_wb_we_o = (mst_gt[0]) ? m_wb_we_0 : m_wb_we_1;

wire  [31:0]  m_wb_dat_0, m_wb_dat_1;
assign m_wb_dat_o = (mst_gt[0]) ? m_wb_dat_0 : m_wb_dat_1;

assign m_wb_cyc_o = (mst_gt[0]) ? m_wb_cyc[0] : m_wb_cyc[1];

wire          m_wb_stb_0, m_wb_stb_1;
assign m_wb_stb_o = (mst_gt[0]) ? m_wb_stb_0 : m_wb_stb_1;

wire          m_wb_ack_0, m_wb_ack_1;
assign m_wb_ack_0 = (mst_gt[0]) ? m_wb_ack_i : 1'b0;
assign m_wb_ack_1 = (mst_gt[1]) ? m_wb_ack_i : 1'b0;

wire          m_wb_err_0, m_wb_err_1;
assign m_wb_err_0 = (mst_gt[0]) ? m_wb_err_i : 1'b0;
assign m_wb_err_1 = (mst_gt[1]) ? m_wb_err_i : 1'b0;


`ifdef ASCII_WAVES
always @(posedge wb_ma.clk)
  begin
     $write("%t: %b | %b:%b %b %h %b %b %h %h %b\n", $time(),
            mst_gt, 
            m_wb_cyc,
            m_wb_cyc_o,
            m_wb_stb_o,
            m_wb_adr_o,
            m_wb_sel_o,
            m_wb_we_o,
            m_wb_dat_i,
            m_wb_dat_o,
            m_wb_ack_i);
  end
`endif

eth_top eth0(// WISHBONE common
             .wb_clk_i(wb_clk_i),
             .wb_rst_i(wb_rst_i), 
             .int_o   (int0),

             // WISHBONE slave
             .wb_adr_i(wb_adr_i[11:2]),
             .wb_sel_i(wb_sel_i),
             .wb_we_i (wb_we_i),
             .wb_cyc_i(wb_cyc_0),
             .wb_stb_i(wb_stb_i),
             .wb_ack_o(wb_ack_0),
             .wb_err_o(wb_err_0),
             .wb_dat_i(wb_dat_i),
             .wb_dat_o(wb_dat_0),
 	
             // WISHBONE master
             .m_wb_adr_o(m_wb_adr_0),
             .m_wb_sel_o(m_wb_sel_0),
             .m_wb_we_o (m_wb_we_0),
             .m_wb_dat_i(m_wb_dat_i),
             .m_wb_dat_o(m_wb_dat_0),
             .m_wb_cyc_o(m_wb_cyc[0]),
             .m_wb_stb_o(m_wb_stb_0),
             .m_wb_ack_i(m_wb_ack_0),
             .m_wb_err_i(m_wb_err_0),

             // MII TX
             .mtx_clk_pad_i(m0tx_clk_pad_i),
             .mtxd_pad_o   (m0txd_pad_o   ),
             .mtxen_pad_o  (m0txen_pad_o  ),
             .mtxerr_pad_o (m0txerr_pad_o ),

             // MII RX
             .mrx_clk_pad_i(m0rx_clk_pad_i),
             .mrxd_pad_i   (m0rxd_pad_i   ),
             .mrxdv_pad_i  (m0rxdv_pad_i  ),
             .mrxerr_pad_i (m0rxerr_pad_i ),
             .mcoll_pad_i  (m0coll_pad_i  ),
             .mcrs_pad_i   (m0crs_pad_i   ),
  
             // MII Management
             .mdc_pad_o (),
             .md_pad_i  (1'b0),
             .md_pad_o  (),
             .md_padoe_o()
);


eth_top eth1(// WISHBONE common
             .wb_clk_i(wb_clk_i),
             .wb_rst_i(wb_rst_i), 
             .int_o   (int1),

             // WISHBONE slave
             .wb_adr_i(wb_adr_i[11:2]),
             .wb_sel_i(wb_sel_i),
             .wb_we_i (wb_we_i),
             .wb_cyc_i(wb_cyc_1),
             .wb_stb_i(wb_stb_i),
             .wb_ack_o(wb_ack_1),
             .wb_err_o(wb_err_1),
             .wb_dat_i(wb_dat_i),
             .wb_dat_o(wb_dat_1),
 	
             // WISHBONE master
             .m_wb_adr_o(m_wb_adr_1),
             .m_wb_sel_o(m_wb_sel_1),
             .m_wb_we_o (m_wb_we_1),
             .m_wb_dat_i(m_wb_dat_i),
             .m_wb_dat_o(m_wb_dat_1),
             .m_wb_cyc_o(m_wb_cyc[1]),
             .m_wb_stb_o(m_wb_stb_1),
             .m_wb_ack_i(m_wb_ack_1),
             .m_wb_err_i(m_wb_err_1),

             // MII TX
             .mtx_clk_pad_i(m1tx_clk_pad_i),
             .mtxd_pad_o   (m1txd_pad_o   ),
             .mtxen_pad_o  (m1txen_pad_o  ),
             .mtxerr_pad_o (m1txerr_pad_o ),

             // MII RX
             .mrx_clk_pad_i(m1rx_clk_pad_i),
             .mrxd_pad_i   (m1rxd_pad_i   ),
             .mrxdv_pad_i  (m1rxdv_pad_i  ),
             .mrxerr_pad_i (m1rxerr_pad_i ),
             .mcoll_pad_i  (m1coll_pad_i  ),
             .mcrs_pad_i   (m1crs_pad_i   ),
  
             // MII Management
             .mdc_pad_o (),
             .md_pad_i  (1'b0),
             .md_pad_o  (),
             .md_padoe_o()
);


endmodule
