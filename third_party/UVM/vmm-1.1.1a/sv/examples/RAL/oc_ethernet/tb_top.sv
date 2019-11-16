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


`include "timescale.v"

`include "wb_if.sv"
`include "mii_if.sv"

module tb_top;

// Clock and reset drivers
bit tx_clk = 0;
bit rx_clk = 0;
bit wb_clk;
bit rst = 0;


//
// Wishbone Signals
//
wb_if wb_sl();   // Slave interface on DUT
wb_if wb_ma();   // Master interface on DUT
wire wb_int;

assign wb_ma.clk = wb_clk;
assign wb_sl.clk = wb_clk;
assign wb_ma.rst = rst;
assign wb_sl.rst = rst;
assign wb_ma.adr[63:32] = 32'h0000_0000;

//
// MII Signals
//
mii_if mii();

assign mii.tx_clk = tx_clk;

wire          Mdi_I;
wire          Mdo_O;
wire          Mdo_OE;
tri           Mdio_IO;
wire          Mdc_O;

//
// DUT
//
eth_top dut (// WISHBONE common
             .wb_clk_i(wb_sl.clk),
             .wb_rst_i(wb_sl.rst), 
             .int_o   (wb_int),

             // WISHBONE slave
             .wb_adr_i(wb_sl.adr[11:2]),
             .wb_sel_i(wb_sl.sel[3:0]),
             .wb_we_i (wb_sl.we), 
             .wb_cyc_i(wb_sl.cyc),
             .wb_stb_i(wb_sl.stb),
             .wb_ack_o(wb_sl.ack), 
             .wb_err_o(wb_sl.err),
             .wb_dat_i(wb_sl.wdat[31:0]),
             .wb_dat_o(wb_sl.rdat[31:0]), 
 	
             // WISHBONE master
             .m_wb_adr_o(wb_ma.adr[31:0]),
             .m_wb_sel_o(wb_ma.sel[3:0]),
             .m_wb_we_o (wb_ma.we), 
             .m_wb_dat_i(wb_ma.rdat[31:0]),
             .m_wb_dat_o(wb_ma.wdat[31:0]),
             .m_wb_cyc_o(wb_ma.cyc), 
             .m_wb_stb_o(wb_ma.stb),
             .m_wb_ack_i(wb_ma.ack),
             .m_wb_err_i(wb_ma.err), 

`ifdef ETH_WISHBONE_B3
             .m_wb_cti_o(wb_ma.cti),
             .m_wb_bte_o(wb_ma.bte),
`endif

             // MII TX
             .mtx_clk_pad_i(mii.tx_clk),
             .mtxd_pad_o   (mii.txd),
             .mtxen_pad_o  (mii.tx_en),
             .mtxerr_pad_o (mii.tx_err),

             // MII RX
             .mrx_clk_pad_i(mii.rx_clk),
             .mrxd_pad_i   (mii.rxd),
             .mrxdv_pad_i  (mii.rx_dv),
             .mrxerr_pad_i (mii.rx_err), 
             .mcoll_pad_i  (mii.col),
             .mcrs_pad_i   (mii.crs), 
  
             // MII Management
             .mdc_pad_o (Mdc_O),
             .md_pad_i  (Mdi_I),
             .md_pad_o  (Mdo_O),
             .md_padoe_o(Mdo_OE)
  
             // Bist
`ifdef ETH_BIST
             ,
             .mbist_si_i   (1'b0),
             .mbist_so_o   (),
             .mbist_ctrl_i (3'b001) // {enable, clock, reset}
`endif
);


//
// Tristated busses
//
assign Mdio_IO = Mdo_OE ? Mdo_O : 1'bz ;
assign Mdi_I   = Mdio_IO;


//
// Clock generators
//
always
begin
  #15; wb_clk = 0;
  #15; wb_clk = 1;
end
endmodule: tb_top
