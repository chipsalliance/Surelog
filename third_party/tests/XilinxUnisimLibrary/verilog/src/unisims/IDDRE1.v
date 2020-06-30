///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2015 Xilinx, Inc.
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
//   ____   ____
//  /   /\/   / 
// /___/  \  /     Vendor      : Xilinx 
// \   \   \/      Version     : 2015.3
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        Dedicated Dual Data Rate (DDR) Input Register
// /___/   /\      Filename    : IDDRE1.v
// \   \  /  \ 
//  \___\/\___\                    
//                                 
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//    10/22/14 - Added #1 to $finish (CR 808642).
//    05/29/15 - Added IS_CB_INVERTED, specify block
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module IDDRE1 #(
  `ifdef XIL_TIMING
  parameter LOC = "UNPLACED",  
  `endif
  parameter DDR_CLK_EDGE = "OPPOSITE_EDGE",
  parameter [0:0] IS_CB_INVERTED = 1'b0,
  parameter [0:0] IS_C_INVERTED = 1'b0
)(
  output Q1,
  output Q2,

  input C,
  input CB,
  input D,
  input R
);
  
// define constants
  localparam MODULE_NAME = "IDDRE1";

// Parameter encodings and registers
  localparam DDR_CLK_EDGE_OPPOSITE_EDGE = 0;
  localparam DDR_CLK_EDGE_SAME_EDGE = 1;
  localparam DDR_CLK_EDGE_SAME_EDGE_PIPELINED = 2;
  
  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
  `ifdef XIL_DR
  `include "IDDRE1_dr.v"
  `else
  localparam [152:1] DDR_CLK_EDGE_REG = DDR_CLK_EDGE;
  localparam [0:0] IS_CB_INVERTED_REG = IS_CB_INVERTED;
  localparam [0:0] IS_C_INVERTED_REG = IS_C_INVERTED;
  `endif

  wire [1:0] DDR_CLK_EDGE_BIN;
  wire IS_CB_INVERTED_BIN;
  wire IS_C_INVERTED_BIN;

  `ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
  `else
  reg attr_test = 1'b0;
  `endif
  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR;

  wire CB_in;
  wire C_in;
  wire D_in;
  wire R_in;

`ifdef XIL_TIMING
  wire CB_delay;
  wire C_delay;
  wire D_delay;
  wire R_delay;
`endif
  

`ifdef XIL_TIMING
  assign CB_in = (CB === 1'bz) || (CB_delay ^ IS_CB_INVERTED_BIN); // rv 1
  assign C_in = C_delay ^ IS_C_INVERTED_BIN;
  assign D_in = D_delay;
  assign R_in = R_delay;
`else
  assign CB_in = (CB === 1'bz) || (CB ^ IS_CB_INVERTED_BIN); // rv 1
  assign C_in = C ^ IS_C_INVERTED_BIN;
  assign D_in = D;
  assign R_in = R;
`endif

  assign DDR_CLK_EDGE_BIN = 
    (DDR_CLK_EDGE_REG == "OPPOSITE_EDGE") ? DDR_CLK_EDGE_OPPOSITE_EDGE :
    (DDR_CLK_EDGE_REG == "SAME_EDGE") ? DDR_CLK_EDGE_SAME_EDGE :
    (DDR_CLK_EDGE_REG == "SAME_EDGE_PIPELINED") ? DDR_CLK_EDGE_SAME_EDGE_PIPELINED :
    DDR_CLK_EDGE_OPPOSITE_EDGE;

  assign IS_CB_INVERTED_BIN = IS_CB_INVERTED_REG;

  assign IS_C_INVERTED_BIN = IS_C_INVERTED_REG;

  initial begin
    #1;
    trig_attr = ~trig_attr;
  end

  always @ (trig_attr) begin
  #1;
    if ((attr_test == 1'b1) ||
        ((DDR_CLK_EDGE_REG != "OPPOSITE_EDGE") &&
         (DDR_CLK_EDGE_REG != "SAME_EDGE") &&
         (DDR_CLK_EDGE_REG != "SAME_EDGE_PIPELINED"))) begin
      $display("Error: [Unisim %s-101] DDR_CLK_EDGE attribute is set to %s.  Legal values for this attribute are OPPOSITE_EDGE, SAME_EDGE or SAME_EDGE_PIPELINED. Instance: %m", MODULE_NAME, DDR_CLK_EDGE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((IS_CB_INVERTED_REG !== 1'b0) && (IS_CB_INVERTED_REG !== 1'b1))) begin
      $display("Error: [Unisim %s-103] IS_CB_INVERTED attribute is set to %b.  Legal values for this attribute are 1'b0 to 1'b1. Instance: %m", MODULE_NAME, IS_CB_INVERTED_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((IS_C_INVERTED_REG !== 1'b0) && (IS_C_INVERTED_REG !== 1'b1))) begin
      $display("Error: [Unisim %s-104] IS_C_INVERTED attribute is set to %b.  Legal values for this attribute are 1'b0 to 1'b1. Instance: %m", MODULE_NAME, IS_C_INVERTED_REG);
      attr_err = 1'b1;
    end

    if (attr_err == 1'b1) #1 $finish;
  end

`ifdef XIL_TIMING
  reg notifier;
`endif

// begin behavioral model

  reg Q1_out;
  reg Q2_out;

  assign Q1 = Q1_out;
  assign Q2 = Q2_out;

  reg q1_out_int,q1_out_pipelined,q2_out_same_edge_int,q2_out_int;

  always @(glblGSR or R_in) begin
    if (glblGSR == 1'b1) begin
      assign q1_out_int = 0;
      assign q1_out_pipelined = 0;
      assign q2_out_same_edge_int = 0;
      assign q2_out_int = 0;
    end else if (glblGSR == 1'b0) begin
      if (R_in == 1'b1) begin
        assign q1_out_int = 0;
        assign q1_out_pipelined = 0;
        assign q2_out_same_edge_int = 0;
        assign q2_out_int = 0;
      end else if (R_in == 1'b0) begin
        deassign q1_out_int;
        deassign q1_out_pipelined;
        deassign q2_out_same_edge_int;
        deassign q2_out_int;
      end
    end
  end

  always @(posedge C_in) begin
    if (R_in == 1'b1) begin
      q1_out_int <= 1'b0;
      q1_out_pipelined <= 1'b0;
      q2_out_same_edge_int <= 1'b0;
    end else if (R_in == 1'b0) begin
      q1_out_int <= D_in;
      q1_out_pipelined <= q1_out_int;
      q2_out_same_edge_int <= q2_out_int;
    end
  end

  always @(posedge CB_in) begin
    if (R_in == 1'b1)
      q2_out_int <= 1'b0;
    else if (R_in == 1'b0)
      q2_out_int <= D_in;
  end
  
  always @(C_in or q1_out_int or q2_out_int or q2_out_same_edge_int or q1_out_pipelined) begin
    case (DDR_CLK_EDGE_REG)
      "OPPOSITE_EDGE" : begin
        Q1_out <= q1_out_int;
        Q2_out <= q2_out_int;
      end
      "SAME_EDGE" : begin
        Q1_out <= q1_out_int;
        Q2_out <= q2_out_same_edge_int;
      end
      "SAME_EDGE_PIPELINED" : begin
        Q1_out <= q1_out_pipelined;
        Q2_out <= q2_out_same_edge_int;
      end
      default : begin
        $display("Error: [Unisim %s-104] Attribute Syntax Error : The attribute DDR_CLK_EDGE on IDDRE1 instance is set to %s.  Legal values for this attribute are OPPOSITE_EDGE, SAME_EDGE or SAME_EDGE_PIPELINED.Instance: %m", MODULE_NAME,DDR_CLK_EDGE);
        $finish;
      end
    endcase // case(DDR_CLK_EDGE_REG)
  end // always @ (C_in or q1_out_int or q2_out_int or q2_out_same_edge_int or q1_out_pipelined)

`ifdef XIL_TIMING
  reg r_enable = 1'b1;
  always @(posedge R_in) r_enable = ~glblGSR && ((Q1_out !== 1'b0) || (Q2_out !== 1'b0));
`endif

// end behavioral model

`ifdef XIL_TIMING

  wire c_en_n;
  wire c_en_p;
  wire cb_en_n;
  wire cb_en_p;
  
  assign c_en_n =  IS_C_INVERTED_BIN;
  assign c_en_p = ~IS_C_INVERTED_BIN;
  assign cb_en_n =  IS_CB_INVERTED_BIN;
  assign cb_en_p = ~IS_CB_INVERTED_BIN;

`endif

  specify
    (C => Q1) = (100:100:100, 100:100:100);
    (C => Q2) = (100:100:100, 100:100:100);
    (CB => Q1) = (100:100:100, 100:100:100);
    (CB => Q2) = (100:100:100, 100:100:100);
    (D => Q1) = (0:0:0, 0:0:0);
    (posedge R => (Q1 +: 0)) = (100:100:100, 100:100:100);
    (posedge R => (Q2 +: 0)) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $period (negedge C, 0:0:0, notifier);
    $period (negedge CB, 0:0:0, notifier);
    $period (posedge C, 0:0:0, notifier);
    $period (posedge CB, 0:0:0, notifier);
    $recrem (negedge R, negedge C, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, R_delay, C_delay);
    $recrem (negedge R, negedge CB, 0:0:0, 0:0:0, notifier, cb_en_n, cb_en_n, R_delay, CB_delay);
    $recrem (negedge R, posedge C, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, R_delay, C_delay);
    $recrem (negedge R, posedge CB, 0:0:0, 0:0:0, notifier, cb_en_p, cb_en_p, R_delay, CB_delay);
    $recrem (posedge R, negedge C, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, R_delay, C_delay);
    $recrem (posedge R, negedge CB, 0:0:0, 0:0:0, notifier, cb_en_n, cb_en_n, R_delay, CB_delay);
    $recrem (posedge R, posedge C, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, R_delay, C_delay);
    $recrem (posedge R, posedge CB, 0:0:0, 0:0:0, notifier, cb_en_p, cb_en_p, R_delay, CB_delay);
    $setuphold (negedge C, negedge D, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, C_delay, D_delay);
    $setuphold (negedge C, negedge R, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, C_delay, R_delay);
    $setuphold (negedge C, posedge D, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, C_delay, D_delay);
    $setuphold (negedge C, posedge R, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, C_delay, R_delay);
    $setuphold (negedge CB, negedge D, 0:0:0, 0:0:0, notifier, cb_en_n, cb_en_n, CB_delay, D_delay);
    $setuphold (negedge CB, posedge D, 0:0:0, 0:0:0, notifier, cb_en_n, cb_en_n, CB_delay, D_delay);
    $setuphold (posedge C, negedge D, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, C_delay, D_delay);
    $setuphold (posedge C, negedge R, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, C_delay, R_delay);
    $setuphold (posedge C, posedge D, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, C_delay, D_delay);
    $setuphold (posedge C, posedge R, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, C_delay, R_delay);
    $setuphold (posedge CB, negedge D, 0:0:0, 0:0:0, notifier, cb_en_p, cb_en_p, CB_delay, D_delay);
    $setuphold (posedge CB, posedge D, 0:0:0, 0:0:0, notifier, cb_en_p, cb_en_p, CB_delay, D_delay);
    $width (negedge C, 0:0:0, 0, notifier);
    $width (negedge CB, 0:0:0, 0, notifier);
    $width (negedge R &&& r_enable, 0:0:0, 0, notifier);
    $width (posedge C, 0:0:0, 0, notifier);
    $width (posedge CB, 0:0:0, 0, notifier);
    $width (posedge R &&& r_enable, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
