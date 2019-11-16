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


`timescale 1ns/1ns

`include "mii_if.sv"

module top;

`ifdef VCD
initial $vcdpluson;
`endif

mii_if if0();

reg tx_clk=0, rx_clk=0;
reg rst = 1'b0;
initial #101 rst = 1'b1;
assign if0.rst = rst;
assign if0.tx_clk = tx_clk;
`ifndef ASCII_WAVES
assign if0.rx_clk = rx_clk;
`else
assign if0.rx_clk = tx_clk;
`endif
always begin  // 10Mb/s
   #25;
   tx_clk = 1'b0;
   #25;
   rx_clk = 1'b0;
   #25;
   tx_clk = 1'b1;
   #25;
   rx_clk = 1'b1;
end

`ifdef ASCII_WAVES
always @(posedge tx_clk)
  begin
      $write("%t: %b %h %b %h %b %b\n",
             $time(), if0.tx_en, if0.txd, if0.rx_dv, if0.rxd, if0.crs, if0.col);
  end
`endif

endmodule
