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


`ifndef MII_MAC_BFM__SV
`define MII_MAC_BFM__SV

// Example 4-86
// Example 4-87
`ifndef ALTERNATIVE_4_166
module mii_mac_bfm(output [3:0] txd,
                   output       tx_en,
                   output       tx_err,
                   input        tx_clk,
                   input  [3:0] rxd,
                   input        rx_dv,
                   input        rx_err,
                   input        rx_clk,
                   input        crs,
                   input        col);

mii_if sigs();
assign txd         = sigs.txd;
assign tx_en       = sigs.tx_en;
assign tx_err      = sigs.tx_err;
assign sigs.tx_clk = tx_clk;
assign sigs.rxd    = rxd;
assign sigs.rx_dv  = rx_dv;
assign sigs.rx_err = rx_err;
assign sigs.rx_clk = rx_clk;
assign sigs.crs    = crs;
assign sigs.col    = col;

`else

// Example 4-88
module mii_mac_bfm(mii_if sigs);

`endif


parameter stream_id = -1;


mii_cfg              cfg;
mii_mac_layer        xact;
// Example 4-89
eth_frame_atomic_gen src;

integer tx_count = 0;

initial
begin
   string inst;
   $sformat(inst, "%m");
   cfg = new;
   xact = new(inst, stream_id, cfg, sigs.mac_layer);
   xact.start_xactor();
   src  = new(inst, stream_id, xact.tx_chan);
end

// Example 4-90
task automatic tx_frame(input bit [47:0] da,
              input bit [47:0] sa,
              input bit [15:0] len1);

   eth_frame fr = new;
   bit ok;
   bit dropped;

   fr.stream_id = stream_id;
   fr.data_id = tx_count++;

   ok = fr.randomize() with {dst     == da;
                             src     == sa;
                             len_typ == len1;
                             format  == eth_frame::UNTAGGED;};
   if (!ok) begin
      `vmm_error(xact.log, "tx_frame(): Unable to randomize remainder of the frame");
      return;
   end

   src.inject(fr, dropped);
endtask: tx_frame
   
endmodule: mii_mac_bfm

`endif
