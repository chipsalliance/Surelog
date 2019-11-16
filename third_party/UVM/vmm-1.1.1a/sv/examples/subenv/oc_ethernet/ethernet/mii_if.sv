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


`ifndef MII_IF__SV
`define MII_IF__SV

`include "vmm.sv"

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
   logic      crs;
   logic      col;
   wire       rst;
   wire [1:20] tx_error_flags;
   bit        mii_FullDuplex = 0;

   clocking mtx @(posedge tx_clk);
      output txd, tx_en, tx_err;
   endclocking

   clocking mrx @(posedge rx_clk);
      input rxd, rx_dv, rx_err;
   endclocking

   // Example 4-6
   // Example 4-54
   modport mac_layer (clocking mtx,
                      clocking mrx,
                      input crs,
                      input col);

   clocking ptx @(posedge tx_clk);
      input txd, tx_en, tx_err;
   endclocking

   clocking prx @(posedge rx_clk);
      output rxd, rx_dv, rx_err;
   endclocking

   // Example 4-6
   modport phy_layer (clocking ptx,
                      clocking prx,
                      output crs,
                      output col);


   // Example 4-6
   modport passive   (clocking ptx,
                      clocking mrx,
                      input crs,
                      input col);
endinterface: mii_if

`endif
