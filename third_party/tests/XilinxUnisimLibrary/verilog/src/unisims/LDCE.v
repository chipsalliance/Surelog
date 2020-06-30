///////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2014 Xilinx, Inc.
// 
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
///////////////////////////////////////////////////////////////////////////////
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor : Xilinx
// \   \   \/     Version : 2014.4
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                  Transparent Data Latch with Asynchronous Clear and Gate Enable
// /___/   /\     Filename : LDCE.v
// \   \  /  \
//  \___\/\___\
//
// Revision:
//    08/25/10 - Initial version.
//    11/01/11 - Disable timing check when set reset active (CR633224)
//    12/08/11 - add MSGON and XON attribures (CR636891)
//    01/16/12 - 640813 - add MSGON and XON functionality
//    04/16/13 - PR683925 - add invertible pin support.
// End Revision

`timescale  1 ps / 1 ps

`celldefine
module LDCE #(
  `ifdef XIL_TIMING //Simprim 
  parameter LOC = "UNPLACED",
  parameter MSGON = "TRUE",
  parameter XON = "TRUE",
  `endif
  parameter [0:0] INIT = 1'b0,
  parameter [0:0] IS_CLR_INVERTED = 1'b0,
  parameter [0:0] IS_G_INVERTED = 1'b0
)(
  output Q,

  input CLR,
  input D,
  input G,
  input GE
);

  wire [0:0] IS_CLR_INVERTED_BIN;
  wire [0:0] IS_G_INVERTED_BIN;

  reg Q_out = INIT;

  wire CLR_in;
  wire D_in;
  wire GE_in;
  wire G_in;

  assign IS_CLR_INVERTED_BIN = IS_CLR_INVERTED;
  assign IS_G_INVERTED_BIN = IS_G_INVERTED;

`ifdef XIL_TIMING
  wire CLR_dly;
  wire D_dly;
  wire GE_dly;
  wire G_dly;

  assign CLR_in = (CLR !== 1'bz) && (CLR_dly ^ IS_CLR_INVERTED_BIN); // rv 0
  assign D_in = D_dly;
  assign G_in = G_dly ^ IS_G_INVERTED_BIN;
  assign GE_in = (GE === 1'bz) || GE_dly; // rv 1
`else
  assign CLR_in = (CLR !== 1'bz) && (CLR ^ IS_CLR_INVERTED_BIN); // rv 0
  assign D_in = D;
  assign G_in = G ^ IS_G_INVERTED_BIN;
  assign GE_in = (GE === 1'bz) || GE; // rv 1
`endif

  assign Q = Q_out;

  reg notifier;
  wire notifier1;
  reg rst_int, set_int;
  wire o_out;

`ifdef XIL_TIMING
  wire ngsr, in_out;
  wire nrst;
  wire in_clk_enable, in_clk_enable_n, in_clk_enable_p;
  wire ce_clk_enable, ce_clk_enable_n, ce_clk_enable_p;
  wire rst_clk_enable, rst_clk_enable1;
  wire tl_enable, tl_enable_n, tl_enable_p;
  wire clk_en_n, clk_en_p;
`endif

  tri0 GSR = glbl.GSR;
    
`ifdef XIL_TIMING
  not (nrst, CLR_in);
  not (ngsr, GSR);
  xor (in_out, D_dly, Q);

  and (in_clk_enable, ngsr, nrst,  GE_in);
  and (ce_clk_enable, ngsr, nrst,  in_out);
  and (rst_clk_enable, ngsr, GE_in);
  and (tl_enable, ngsr, nrst);

  assign notifier1 = (XON == "FALSE") ?  1'bx : notifier;
  assign in_clk_enable_n = (MSGON =="TRUE") && in_clk_enable && IS_G_INVERTED_BIN;
  assign in_clk_enable_p = (MSGON =="TRUE") && in_clk_enable && ~IS_G_INVERTED_BIN;
  assign ce_clk_enable_n = (MSGON =="TRUE") && ce_clk_enable && IS_G_INVERTED_BIN;
  assign ce_clk_enable_p = (MSGON =="TRUE") && ce_clk_enable && ~IS_G_INVERTED_BIN;
  assign rst_clk_enable1 = (MSGON =="FALSE") ? 1'b0 : rst_clk_enable;
  assign tl_enable_n = (MSGON =="TRUE") && tl_enable && IS_G_INVERTED_BIN;
  assign tl_enable_p = (MSGON =="TRUE") && tl_enable && ~IS_G_INVERTED_BIN;
  assign clk_en_n = (MSGON =="TRUE") && IS_G_INVERTED_BIN;
  assign clk_en_p = (MSGON =="TRUE") && ~IS_G_INVERTED_BIN;
`else
  assign notifier1 = 1'bx;
`endif
    
  always @(GSR or CLR_in) begin
    if (GSR) begin
      if (INIT) begin
        rst_int = 1'b0;
        set_int = 1'b1;
      end
      else begin
        rst_int = 1'b1;
        set_int = 1'b0;
      end
    end
    else begin
      rst_int = CLR_in;
      set_int = 1'b0;
    end
  end

  latchsre_ldce (o_out, G_in, D_in, set_int, rst_int, GE_in, notifier1);
    
  always @(o_out)
      Q_out = o_out;

    
  specify
    (D => Q) = (100:100:100, 100:100:100);
    (G => Q) = (100:100:100, 100:100:100);
    (GE => Q) = (0:0:0, 0:0:0);
`ifdef XIL_TIMING
    (CLR => Q) = (0:0:0, 0:0:0);
    (negedge CLR => (Q +: 0)) = (0:0:0, 0:0:0);
    (posedge CLR => (Q +: 0)) = (0:0:0, 0:0:0);
    $period (negedge G, 0:0:0, notifier);
    $period (posedge G, 0:0:0, notifier);
    $recrem (negedge CLR, negedge G, 0:0:0, 0:0:0, notifier,tl_enable_n,tl_enable_n,CLR_dly, G_dly);
    $recrem (negedge CLR, posedge G, 0:0:0, 0:0:0, notifier,tl_enable_p,tl_enable_p,CLR_dly, G_dly);
    $recrem (negedge GE, negedge G, 0:0:0, 0:0:0, notifier,tl_enable_n,tl_enable_n,GE_dly, G_dly);
    $recrem (negedge GE, posedge G, 0:0:0, 0:0:0, notifier,tl_enable_p,tl_enable_p,GE_dly, G_dly);
    $recrem (posedge CLR, negedge G, 0:0:0, 0:0:0, notifier,tl_enable_n,tl_enable_n,CLR_dly, G_dly);
    $recrem (posedge CLR, posedge G, 0:0:0, 0:0:0, notifier,tl_enable_p,tl_enable_p,CLR_dly, G_dly);
    $setuphold (negedge G, negedge CLR, 0:0:0, 0:0:0, notifier,clk_en_n,clk_en_n, G_dly, CLR_dly);
    $setuphold (negedge G, negedge D, 0:0:0, 0:0:0, notifier,in_clk_enable_n,in_clk_enable_n,G_dly,D_dly);
    $setuphold (negedge G, negedge GE, 0:0:0, 0:0:0, notifier,ce_clk_enable_n,ce_clk_enable_n,G_dly,GE_dly);
    $setuphold (negedge G, posedge CLR, 0:0:0, 0:0:0, notifier,clk_en_n,clk_en_n, G_dly, CLR_dly);
    $setuphold (negedge G, posedge D, 0:0:0, 0:0:0, notifier,in_clk_enable_n,in_clk_enable_n,G_dly,D_dly);
    $setuphold (negedge G, posedge GE, 0:0:0, 0:0:0, notifier,ce_clk_enable_n,ce_clk_enable_n,G_dly,GE_dly);
    $setuphold (posedge G, negedge CLR, 0:0:0, 0:0:0, notifier,clk_en_p,clk_en_p, G_dly, CLR_dly);
    $setuphold (posedge G, negedge D, 0:0:0, 0:0:0, notifier,in_clk_enable_p,in_clk_enable_p,G_dly,D_dly);
    $setuphold (posedge G, negedge GE, 0:0:0, 0:0:0, notifier,ce_clk_enable_p,ce_clk_enable_p,G_dly,GE_dly);
    $setuphold (posedge G, posedge CLR, 0:0:0, 0:0:0, notifier,clk_en_p,clk_en_p, G_dly, CLR_dly);
    $setuphold (posedge G, posedge D, 0:0:0, 0:0:0, notifier,in_clk_enable_p,in_clk_enable_p,G_dly,D_dly);
    $setuphold (posedge G, posedge GE, 0:0:0, 0:0:0, notifier,ce_clk_enable_p,ce_clk_enable_p,G_dly,GE_dly);
    $width (negedge CLR, 0:0:0, 0, notifier);
    $width (negedge G, 0:0:0, 0, notifier);
    $width (posedge CLR, 0:0:0, 0, notifier);
    $width (posedge G, 0:0:0, 0, notifier);
    $width (posedge GE, 0:0:0, 0, notifier);
`endif
      specparam PATHPULSE$ = 0;
  endspecify

    
endmodule

`endcelldefine


primitive latchsre_ldce (q, clk, d, set, rst, ge, notifier);

  output q; reg q;
  input clk, d, set, rst, ge, notifier;

  table

    //   clk    d   set   rst   ge  notifier   q     q+;

          1     0    0     0    1      ?   :   ?  :  0;
          1     1    0     0    1      ?   :   ?  :  1;

          0     ?    0     0    ?      ?   :   ?  :  -;
          ?     ?    0     0    0      ?   :   ?  :  -;
          ?     0    0     ?    ?      ?   :   0  :  -;
          ?     1    ?     0    ?      ?   :   1  :  -;

          ?     ?    1     0    ?      ?   :   ?  :  1;
          ?     ?    ?     1    ?      ?   :   ?  :  0;
          0     ?    0     x    ?      ?   :   0  :  0;
          ?     ?    0     x    0      ?   :   0  :  0;
          1     0    0     x    1      ?   :   ?  :  0;
          0     ?    x     0    ?      ?   :   1  :  1;
          ?     ?    x     0    0      ?   :   1  :  1;
          1     1    x     0    1      ?   :   ?  :  1;
          ?     ?    ?     ?    ?      *   :   ?  :  x;

  endtable

endprimitive
