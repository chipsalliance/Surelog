///////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2016 Xilinx, Inc.
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
// \   \   \/     Version : 2017.1
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                  D Flip-Flop with Clock Enable and Asynchronous Preset
// /___/   /\     Filename : FDPE.v
// \   \  /  \
//  \___\/\___\
//
// Revision:
//    08/25/10 - Initial version.
//    10/20/10 - remove unused pin line from table.
//    11/01/11 - Disable timing check when set reset active (CR632017)
//    12/08/11 - add MSGON and XON attributes (CR636891)
//    01/16/12 - 640813 - add MSGON and XON functionality
//    04/16/13 - PR683925 - add invertible pin support.
// End Revision

`timescale  1 ps / 1 ps

`celldefine 

module FDPE #(
  `ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
  parameter MSGON = "TRUE",
  parameter XON = "TRUE",
  `endif
  parameter [0:0] INIT = 1'b1,
  parameter [0:0] IS_C_INVERTED = 1'b0,
  parameter [0:0] IS_D_INVERTED = 1'b0,
  parameter [0:0] IS_PRE_INVERTED = 1'b0
)(
  output Q,
  
  input C,
  input CE,
  input D,
  input PRE
);

    reg [0:0] IS_C_INVERTED_REG = IS_C_INVERTED;
    reg [0:0] IS_D_INVERTED_REG = IS_D_INVERTED;
    reg [0:0] IS_PRE_INVERTED_REG = IS_PRE_INVERTED;
    
    tri0 glblGSR = glbl.GSR;

`ifdef XIL_TIMING
    wire D_dly, C_dly, CE_dly;
    wire PRE_dly;
`endif

    wire PRE_in;

`ifdef XIL_TIMING
    assign PRE_in = (PRE_dly ^ IS_PRE_INVERTED_REG) && (PRE !== 1'bz);
`else
    assign PRE_in = (PRE ^ IS_PRE_INVERTED_REG) && (PRE !== 1'bz);
`endif

// begin behavioral model

  reg Q_out;

  assign #100 Q = Q_out;

    always @(glblGSR or PRE_in)
      if (glblGSR) 
        assign Q_out = INIT;
      else if (PRE_in === 1'b1) 
        assign Q_out = 1'b1;
      else if (PRE_in === 1'bx) 
        assign Q_out = 1'bx;
      else
        deassign Q_out;

`ifdef XIL_TIMING
generate
if (IS_C_INVERTED == 1'b0) begin : generate_block1
  always @(posedge C_dly or posedge PRE_in)
    if (PRE_in || (PRE === 1'bx && Q_out == 1'b1))
      Q_out <= 1'b1;
    else if (CE_dly || (CE === 1'bz) || ((CE === 1'bx) && (Q_out == (D_dly ^ IS_D_INVERTED_REG))))
      Q_out <= D_dly ^ IS_D_INVERTED_REG;
end else begin : generate_block1
  always @(negedge C_dly or posedge PRE_in)
    if (PRE_in || (PRE === 1'bx && Q_out == 1'b1))
      Q_out <= 1'b1;
    else if (CE_dly || (CE === 1'bz) || ((CE === 1'bx) && (Q_out == (D_dly ^ IS_D_INVERTED_REG))))
      Q_out <= D_dly ^ IS_D_INVERTED_REG;
end
endgenerate
`else
generate
if (IS_C_INVERTED == 1'b0) begin : generate_block1
  always @(posedge C or posedge PRE_in)
    if (PRE_in || (PRE === 1'bx && Q_out == 1'b1))
      Q_out <= 1'b1;
    else if (CE || (CE === 1'bz) || ((CE === 1'bx) && (Q_out == (D ^ IS_D_INVERTED_REG))))
      Q_out <= D ^ IS_D_INVERTED_REG;
end else begin : generate_block1
  always @(negedge C or posedge PRE_in)
    if (PRE_in || (PRE === 1'bx && Q_out == 1'b1))
      Q_out <= 1'b1;
    else if (CE || (CE === 1'bz) || ((CE === 1'bx) && (Q_out == (D ^ IS_D_INVERTED_REG))))
      Q_out <= D ^ IS_D_INVERTED_REG;
end
endgenerate
`endif

`ifdef XIL_TIMING
    reg notifier;
    wire notifier1;
`endif

`ifdef XIL_TIMING
    wire ngsr, in_out;
    wire nset;
    wire in_clk_enable, in_clk_enable_p, in_clk_enable_n;
    wire ce_clk_enable, ce_clk_enable_p, ce_clk_enable_n;
    reg init_enable = 1'b1;
    wire set_clk_enable, set_clk_enable_p, set_clk_enable_n;
`endif

`ifdef XIL_TIMING
    not (ngsr, glblGSR);
    xor (in_out, D_dly, IS_D_INVERTED_REG, Q_out);
    not (nset, (PRE_dly ^ IS_PRE_INVERTED_REG) && (PRE !== 1'bz));

    and (in_clk_enable, ngsr, nset, CE || (CE === 1'bz));
    and (ce_clk_enable, ngsr, nset, in_out);
    and (set_clk_enable, ngsr, CE || (CE === 1'bz), D ^ IS_D_INVERTED_REG);
    always @(negedge nset) init_enable = (MSGON =="TRUE") && ~glblGSR && (Q_out ^ INIT);

    assign notifier1 = (XON == "FALSE") ?  1'bx : notifier;
    assign ce_clk_enable_n = (MSGON =="TRUE") && ce_clk_enable && (IS_C_INVERTED == 1'b1);
    assign in_clk_enable_n = (MSGON =="TRUE") && in_clk_enable && (IS_C_INVERTED == 1'b1);
    assign set_clk_enable_n = (MSGON =="TRUE") && set_clk_enable && (IS_C_INVERTED == 1'b1);
    assign ce_clk_enable_p = (MSGON =="TRUE") && ce_clk_enable && (IS_C_INVERTED == 1'b0);
    assign in_clk_enable_p = (MSGON =="TRUE") && in_clk_enable && (IS_C_INVERTED == 1'b0);
    assign set_clk_enable_p = (MSGON =="TRUE") && set_clk_enable && (IS_C_INVERTED == 1'b0);
`endif

// end behavioral model

`ifdef XIL_TIMING
  specify
  (C => Q) = (100:100:100, 100:100:100);
  (negedge PRE => (Q +: 1)) = (0:0:0, 0:0:0);
  (posedge PRE => (Q +: 1)) = (0:0:0, 0:0:0);
  (PRE => Q) = (0:0:0, 0:0:0);
  $period (negedge C &&& CE, 0:0:0, notifier);
  $period (posedge C &&& CE, 0:0:0, notifier);
  $recrem (negedge PRE, negedge C, 0:0:0, 0:0:0, notifier,set_clk_enable_n,set_clk_enable_n,PRE_dly, C_dly);
  $recrem (negedge PRE, posedge C, 0:0:0, 0:0:0, notifier,set_clk_enable_p,set_clk_enable_p,PRE_dly, C_dly);
  $recrem (posedge PRE, negedge C, 0:0:0, 0:0:0, notifier,set_clk_enable_n,set_clk_enable_n,PRE_dly, C_dly);
  $recrem (posedge PRE, posedge C, 0:0:0, 0:0:0, notifier,set_clk_enable_p,set_clk_enable_p,PRE_dly, C_dly);
  $setuphold (negedge C, negedge CE, 0:0:0, 0:0:0, notifier,ce_clk_enable_n,ce_clk_enable_n,C_dly,CE_dly);
  $setuphold (negedge C, negedge D, 0:0:0, 0:0:0, notifier,in_clk_enable_n,in_clk_enable_n,C_dly,D_dly);
  $setuphold (negedge C, posedge CE, 0:0:0, 0:0:0, notifier,ce_clk_enable_n,ce_clk_enable_n,C_dly,CE_dly);
  $setuphold (negedge C, posedge D, 0:0:0, 0:0:0, notifier,in_clk_enable_n,in_clk_enable_n,C_dly,D_dly);
  $setuphold (posedge C, negedge CE, 0:0:0, 0:0:0, notifier,ce_clk_enable_p,ce_clk_enable_p,C_dly,CE_dly);
  $setuphold (posedge C, negedge D, 0:0:0, 0:0:0, notifier,in_clk_enable_p,in_clk_enable_p,C_dly,D_dly);
  $setuphold (posedge C, posedge CE, 0:0:0, 0:0:0, notifier,ce_clk_enable_p,ce_clk_enable_p,C_dly,CE_dly);
  $setuphold (posedge C, posedge D, 0:0:0, 0:0:0, notifier,in_clk_enable_p,in_clk_enable_p,C_dly,D_dly);
  $width (negedge C &&& CE, 0:0:0, 0, notifier);
  $width (negedge PRE &&& init_enable, 0:0:0, 0, notifier);
  $width (posedge C &&& CE, 0:0:0, 0, notifier);
  $width (posedge PRE &&& init_enable, 0:0:0, 0, notifier);
  specparam PATHPULSE$ = 0;
  endspecify
`endif
endmodule

`endcelldefine
