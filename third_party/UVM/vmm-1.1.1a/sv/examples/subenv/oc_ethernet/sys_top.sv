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

module sys_top;

// Clock and reset drivers
bit tx_clk;
bit rx_clk;
bit wb_clk;
bit rst = 0;


//
// Wishbone Signals
//
wb_if wb_sl();   // Slave interface on DUT
wb_if wb_ma();   // Master interface on DUT
wire wb_int0, wb_int1;

assign wb_ma.clk = wb_clk;
assign wb_sl.clk = wb_clk;
assign wb_ma.rst = rst;
assign wb_sl.rst = rst;
assign wb_ma.adr[63:32] = 32'h0000_0000;

//
// MII Signals
//
mii_if mii_0();
mii_if mii_1();

assign mii_0.tx_clk = tx_clk;
assign mii_0.rx_clk = rx_clk;
assign mii_1.tx_clk = tx_clk;
assign mii_1.rx_clk = rx_clk;

//
// DUT
//
dual_eth dut (// WISHBONE common
             .wb_clk_i(wb_sl.clk),
             .wb_rst_i(wb_sl.rst), 
             .int0    (wb_int0),
             .int1    (wb_int1),

             // WISHBONE slave
             .wb_adr_i(wb_sl.adr[31:2]),
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

             // MII TX
             .m0tx_clk_pad_i(mii_0.tx_clk),
             .m0txd_pad_o   (mii_0.txd),
             .m0txen_pad_o  (mii_0.tx_en),
             .m0txerr_pad_o (mii_0.tx_err),

             .m1tx_clk_pad_i(mii_1.tx_clk),
             .m1txd_pad_o   (mii_1.txd),
             .m1txen_pad_o  (mii_1.tx_en),
             .m1txerr_pad_o (mii_1.tx_err),

             // MII RX
             .m0rx_clk_pad_i(mii_0.rx_clk),
             .m0rxd_pad_i   (mii_0.rxd),
             .m0rxdv_pad_i  (mii_0.rx_dv),
             .m0rxerr_pad_i (mii_0.rx_err), 

             .m1rx_clk_pad_i(mii_1.rx_clk),
             .m1rxd_pad_i   (mii_1.rxd),
             .m1rxdv_pad_i  (mii_1.rx_dv),
             .m1rxerr_pad_i (mii_1.rx_err), 

             .m0coll_pad_i  (mii_0.col),
             .m0crs_pad_i   (mii_0.crs), 
  
             .m1coll_pad_i  (mii_1.col),
             .m1crs_pad_i   (mii_1.crs)
);


//
// Clock generators
//
always
begin
  #5; wb_clk = 0;
  #5; wb_clk = 1;
end

always
begin // 100Mb
   #(20) rx_clk = 1;
   #(20) rx_clk = 0;
end

always
begin // 100Mb
   #(20) tx_clk = 1;
   #(20) tx_clk = 0;
end

endmodule: sys_top
