// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2008-2009 Mentor Graphics Corporation
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


`ifndef MII_IF__SV
`define MII_IF__SV

//`include "vmm.sv"

// Example 4-2
interface mii_if();

   wire       tx_clk;
   wire [3:0] txd;
   wire       tx_en;
   wire       tx_err;
   wire       rx_clk;
   wire [3:0] rxd;
   wire       rx_dv;
   wire       rx_err;
   bit        crs;
   bit        col;
   wire       rst;
   wire [1:20] tx_error_flags;
   bit        mii_FullDuplex = 0;

/*
   mii_sva_error_size_type tx_error_flags;
   wire        tx_bad_frame = | tx_error_flags;
   mii_sva_error_size_type rx_error_flags;
   wire        rx_bad_frame = | rx_error_flags;
   mii_sva_cover_size_type tx_cover_flags;
   wire        tx_cover_frame = | tx_cover_flags;
   mii_sva_cover_size_type rx_cover_flags;
   wire        rx_cover_frame = | rx_cover_flags;
*/

   clocking mtx @(posedge tx_clk);
      default input #5 output #3;
      output txd, tx_en, tx_err;
   endclocking

   clocking mrx @(posedge rx_clk);
      default input #5 output #3;
      input rxd, rx_dv, rx_err;
   endclocking

   // Example 4-6
   // Example 4-54
   modport mac_layer (clocking mtx,
                      clocking mrx,
                      input crs,
                      input col);
//                      input tx_error_flags,
//                      input tx_bad_frame);


   clocking ptx @(posedge tx_clk);
      default input #5 output #3;
      input txd, tx_en, tx_err;
   endclocking

   clocking prx @(posedge rx_clk);
      default input #5 output #3;
      output rxd, rx_dv, rx_err;
   endclocking

   // Example 4-6
   modport phy_layer (clocking ptx,
                      clocking prx,
                      output crs,
                      output col);
//                      input  tx_error_flags,
//                      input  tx_bad_frame);


   // Example 4-6
   modport passive   (clocking ptx,
                      clocking mrx,
                      input crs,
                      input col);
//                      input tx_error_flags,
//                      input tx_bad_frame);

`ifdef SVA_CHECKERS
   mii_sva_checker
//       #(   ) // some params other than the defaults?
     sva_checker
       (.reset_n(rst),
        .TX_CLK (tx_clk),
        .TX_EN  (tx_en),
        .TX_ER  (tx_err),
        .TXD    (txd),
        .COL    (col),
        .CRS    (crs),
        .RX_CLK (rx_clk),
        .RX_DV  (rx_dv),
        .RX_ER  (rx_err),
        .RXD    (rxd),
        .mii_FullDuplex(mii_FullDuplex) //,
//        .TX_FrameError(tx_error_flags),
//        .RX_FrameError(rx_error_flags),
//        .TX_FrameCover(tx_cover_flags),
//        .RX_FrameCover(rx_cover_flags)
         );
`endif

endinterface: mii_if

`ifdef SVA_CHECKERS
`include "mii_sva_types.sv"
`include "mii_sva_checker.sv"
`endif

`endif
