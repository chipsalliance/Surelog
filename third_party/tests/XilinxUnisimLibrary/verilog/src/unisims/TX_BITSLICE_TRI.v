///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2016 Xilinx, Inc.
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
// /___/  \  /     Vendor      : Xilinx
// \   \   \/      Version     : 2016.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        TX_BITSLICE_TRI
// /___/   /\      Filename    : TX_BITSLICE_TRI.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module TX_BITSLICE_TRI #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter integer DATA_WIDTH = 8,
  parameter DELAY_FORMAT = "TIME",
  parameter DELAY_TYPE = "FIXED",
  parameter integer DELAY_VALUE = 0,
  parameter [0:0] INIT = 1'b1,
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [0:0] IS_RST_DLY_INVERTED = 1'b0,
  parameter [0:0] IS_RST_INVERTED = 1'b0,
  parameter NATIVE_ODELAY_BYPASS = "FALSE",
  parameter OUTPUT_PHASE_90 = "FALSE",
  parameter real REFCLK_FREQUENCY = 300.0,
  parameter SIM_DEVICE = "ULTRASCALE",
  parameter real SIM_VERSION = 2.0,
  parameter UPDATE_MODE = "ASYNC"
)(
  output [39:0] BIT_CTRL_OUT,
  output [8:0] CNTVALUEOUT,
  output TRI_OUT,

  input [39:0] BIT_CTRL_IN,
  input CE,
  input CLK,
  input [8:0] CNTVALUEIN,
  input EN_VTC,
  input INC,
  input LOAD,
  input RST,
  input RST_DLY
);

// define constants
  localparam MODULE_NAME = "TX_BITSLICE_TRI";
  localparam in_delay    = 0;
  localparam out_delay   = 0;
  localparam inclk_delay    = 0;
  localparam outclk_delay   = 0;

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "TX_BITSLICE_TRI_dr.v"
`else
  localparam [31:0] DATA_WIDTH_REG = DATA_WIDTH;
  localparam [40:1] DELAY_FORMAT_REG = DELAY_FORMAT;
  localparam [64:1] DELAY_TYPE_REG = DELAY_TYPE;
  localparam [31:0] DELAY_VALUE_REG = DELAY_VALUE;
  localparam [0:0] INIT_REG = INIT;
  localparam [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
  localparam [0:0] IS_RST_DLY_INVERTED_REG = IS_RST_DLY_INVERTED;
  localparam [0:0] IS_RST_INVERTED_REG = IS_RST_INVERTED;
  localparam [40:1] NATIVE_ODELAY_BYPASS_REG = NATIVE_ODELAY_BYPASS;
  localparam [40:1] OUTPUT_PHASE_90_REG = OUTPUT_PHASE_90;
  localparam real REFCLK_FREQUENCY_REG = REFCLK_FREQUENCY;
  localparam [152:1] SIM_DEVICE_REG = SIM_DEVICE;
  localparam real SIM_VERSION_REG = SIM_VERSION;
  localparam [48:1] UPDATE_MODE_REG = UPDATE_MODE;
`endif

  localparam [0:0] DC_ADJ_EN_REG = 1'b0;
  localparam [2:0] FDLY_REG = 3'b010;
  localparam [2:0] SPARE_REG = 3'b000;

  wire IS_CLK_INVERTED_BIN;
  wire IS_RST_DLY_INVERTED_BIN;
  wire IS_RST_INVERTED_BIN;
  wire [63:0] REFCLK_FREQUENCY_BIN;
  wire [63:0] SIM_VERSION_BIN;

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif
  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR;

  wire CDATAOUT_out;
  wire TRI_OUT_out;
  wire [39:0] BIT_CTRL_OUT_out;
  wire [8:0] CNTVALUEOUT_out;

  wire TRI_OUT_delay;
  wire [39:0] BIT_CTRL_OUT_delay;
  wire [8:0] CNTVALUEOUT_delay;

  wire CDATAIN0_in;
  wire CDATAIN1_in;
  wire CE_in;
  wire CLK_in;
  wire EN_VTC_in;
  wire INC_in;
  wire LOAD_in;
  wire OFD_CE_in;
  wire RST_DLY_in;
  wire RST_in;
  wire [39:0] BIT_CTRL_IN_in;
  wire [8:0] CNTVALUEIN_in;

  wire CE_delay;
  wire CLK_delay;
  wire EN_VTC_delay;
  wire INC_delay;
  wire LOAD_delay;
  wire RST_DLY_delay;
  wire RST_delay;
  wire [39:0] BIT_CTRL_IN_delay;
  wire [8:0] CNTVALUEIN_delay;

  assign #(out_delay) BIT_CTRL_OUT = BIT_CTRL_OUT_delay;
  assign #(out_delay) CNTVALUEOUT = CNTVALUEOUT_delay;
  assign #(out_delay) TRI_OUT = TRI_OUT_delay;

`ifndef XIL_TIMING // inputs with timing checks
  assign #(inclk_delay) CLK_delay = CLK;

  assign #(in_delay) CE_delay = CE;
  assign #(in_delay) CNTVALUEIN_delay = CNTVALUEIN;
  assign #(in_delay) INC_delay = INC;
  assign #(in_delay) LOAD_delay = LOAD;
`endif

// inputs with no timing checks
  assign #(in_delay) BIT_CTRL_IN_delay = BIT_CTRL_IN;
  assign #(in_delay) EN_VTC_delay = EN_VTC;
  assign #(in_delay) RST_DLY_delay = RST_DLY;
  assign #(in_delay) RST_delay = RST;

  assign BIT_CTRL_OUT_delay = BIT_CTRL_OUT_out;
  assign CNTVALUEOUT_delay = CNTVALUEOUT_out;
  assign TRI_OUT_delay = TRI_OUT_out;

  assign BIT_CTRL_IN_in = BIT_CTRL_IN_delay;
  assign CE_in = CE_delay;
  assign CLK_in = CLK_delay ^ IS_CLK_INVERTED_BIN;
  assign CNTVALUEIN_in = CNTVALUEIN_delay;
  assign EN_VTC_in = EN_VTC_delay;
  assign INC_in = INC_delay;
  assign LOAD_in = LOAD_delay;
  assign RST_DLY_in = RST_DLY_delay ^ IS_RST_DLY_INVERTED_BIN;
  assign RST_in = RST_delay ^ IS_RST_INVERTED_BIN;


  assign IS_CLK_INVERTED_BIN = IS_CLK_INVERTED_REG;
  
  assign IS_RST_DLY_INVERTED_BIN = IS_RST_DLY_INVERTED_REG;
  
  assign IS_RST_INVERTED_BIN = IS_RST_INVERTED_REG;
  
  assign REFCLK_FREQUENCY_BIN = REFCLK_FREQUENCY_REG * 1000;
  
  assign SIM_VERSION_BIN = SIM_VERSION_REG * 1000;
  
  initial begin
    #1;
    trig_attr = ~trig_attr;
  end
  
  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((DATA_WIDTH_REG != 8) &&
         (DATA_WIDTH_REG != 4))) begin
      $display("Error: [Unisim %s-101] DATA_WIDTH attribute is set to %d.  Legal values for this attribute are 8 or 4. Instance: %m", MODULE_NAME, DATA_WIDTH_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((DELAY_FORMAT_REG != "TIME") &&
         (DELAY_FORMAT_REG != "COUNT"))) begin
      $display("Error: [Unisim %s-103] DELAY_FORMAT attribute is set to %s.  Legal values for this attribute are TIME or COUNT. Instance: %m", MODULE_NAME, DELAY_FORMAT_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((DELAY_TYPE_REG != "FIXED") &&
         (DELAY_TYPE_REG != "VAR_LOAD") &&
         (DELAY_TYPE_REG != "VARIABLE"))) begin
      $display("Error: [Unisim %s-104] DELAY_TYPE attribute is set to %s.  Legal values for this attribute are FIXED, VAR_LOAD or VARIABLE. Instance: %m", MODULE_NAME, DELAY_TYPE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        (SIM_DEVICE_REG == "ULTRASCALE" && ((DELAY_VALUE_REG < 0) || (DELAY_VALUE_REG > 1250)))) begin
      $display("Error: [Unisim %s-105] DELAY_VALUE attribute is set to %d.  Legal values for this attribute are 0 to 1250. Instance: %m", MODULE_NAME, DELAY_VALUE_REG);
      attr_err = 1'b1;
    end
    if ((attr_test == 1'b1) ||
        (SIM_DEVICE_REG != "ULTRASCALE" && ((DELAY_VALUE_REG < 0) || (DELAY_VALUE_REG > 1100)))) begin
      $display("Error: [Unisim %s-105] DELAY_VALUE attribute is set to %d.  Legal values for this attribute are 0 to 1100. Instance: %m", MODULE_NAME, DELAY_VALUE_REG);
      attr_err = 1'b1;
    end    
    if ((attr_test == 1'b1) ||
        ((NATIVE_ODELAY_BYPASS_REG != "FALSE") &&
         (NATIVE_ODELAY_BYPASS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-111] NATIVE_ODELAY_BYPASS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, NATIVE_ODELAY_BYPASS_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((OUTPUT_PHASE_90_REG != "FALSE") &&
         (OUTPUT_PHASE_90_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-112] OUTPUT_PHASE_90 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, OUTPUT_PHASE_90_REG);
      attr_err = 1'b1;
    end
    
    
    if ((attr_test == 1'b1) ||
        (DELAY_FORMAT_REG != "COUNT" && SIM_DEVICE_REG != "ULTRASCALE" && (REFCLK_FREQUENCY_REG < 300.0 || REFCLK_FREQUENCY_REG > 2667.0))) begin
      $display("Error: [Unisim %s-113] REFCLK_FREQUENCY attribute is set to %f.  Legal values for this attribute are 300.0 to 2667.0. Instance: %m", MODULE_NAME, REFCLK_FREQUENCY_REG);
      attr_err = 1'b1;
    end
    if ((attr_test == 1'b1) ||
        (DELAY_FORMAT_REG != "COUNT" && SIM_DEVICE_REG == "ULTRASCALE" && (REFCLK_FREQUENCY_REG < 200.0 || REFCLK_FREQUENCY_REG > 2400.0))) begin
      $display("Error: [Unisim %s-113] REFCLK_FREQUENCY attribute is set to %f.  Legal values for this attribute are 200.0 to 2400.0. Instance: %m", MODULE_NAME, REFCLK_FREQUENCY_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2"))) begin
      $display("Error: [Unisim %s-114] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE, ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1 or ULTRASCALE_PLUS_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
       ((SIM_VERSION_REG != 2.0) &&
        (SIM_VERSION_REG != 1.0))) begin
      $display("Error: [Unisim %s-115] SIM_VERSION attribute is set to %f.  Legal values for this attribute are 2.0 or 1.0. Instance: %m", MODULE_NAME, SIM_VERSION_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((UPDATE_MODE_REG != "ASYNC") &&
         (UPDATE_MODE_REG != "MANUAL") &&
         (UPDATE_MODE_REG != "SYNC"))) begin
      $display("Error: [Unisim %s-116] UPDATE_MODE attribute is set to %s.  Legal values for this attribute are ASYNC, MANUAL or SYNC. Instance: %m", MODULE_NAME, UPDATE_MODE_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end


  assign CDATAIN0_in = 1'b1; // tie off
  assign CDATAIN1_in = 1'b1; // tie off
  assign OFD_CE_in = 1'b0; // tie off

generate

if ((SIM_DEVICE == "ULTRASCALE_PLUS") || (SIM_DEVICE == "ULTRASCALE_PLUS_ES1") || (SIM_DEVICE == "ULTRASCALE_PLUS_ES2")) begin : generate_block1
  SIP_TX_BITSLICE_TRI_D1 SIP_TX_BITSLICE_TRI_INST (
    .DATA_WIDTH (DATA_WIDTH_REG),
    .DC_ADJ_EN (DC_ADJ_EN_REG),
    .DELAY_FORMAT (DELAY_FORMAT_REG),
    .DELAY_TYPE (DELAY_TYPE_REG),
    .DELAY_VALUE (DELAY_VALUE_REG),
    .FDLY (FDLY_REG),
    .SPARE (SPARE_REG),
    .INIT (INIT_REG),
    .NATIVE_ODELAY_BYPASS (NATIVE_ODELAY_BYPASS_REG),
    .OUTPUT_PHASE_90 (OUTPUT_PHASE_90_REG),
    .REFCLK_FREQUENCY (REFCLK_FREQUENCY_BIN),
    .UPDATE_MODE (UPDATE_MODE_REG),
    .BIT_CTRL_OUT (BIT_CTRL_OUT_out),
    .CDATAOUT (CDATAOUT_out),
    .CNTVALUEOUT (CNTVALUEOUT_out),
    .TRI_OUT (TRI_OUT_out),
    .BIT_CTRL_IN (BIT_CTRL_IN_in),
    .CDATAIN0 (CDATAIN0_in),
    .CDATAIN1 (CDATAIN1_in),
    .CE (CE_in),
    .CLK (CLK_in),
    .CNTVALUEIN (CNTVALUEIN_in),
    .EN_VTC (EN_VTC_in),
    .INC (INC_in),
    .LOAD (LOAD_in),
    .OFD_CE (OFD_CE_in),
    .RST (RST_in),
    .RST_DLY (RST_DLY_in),
    .GSR (glblGSR)
  );
end  
else if (SIM_DEVICE == "ULTRASCALE") begin : generate_block1
  SIP_TX_BITSLICE_TRI_K2 SIP_TX_BITSLICE_TRI_INST (
    .DATA_WIDTH (DATA_WIDTH_REG),
    .DC_ADJ_EN (DC_ADJ_EN_REG),
    .DELAY_FORMAT (DELAY_FORMAT_REG),
    .DELAY_TYPE (DELAY_TYPE_REG),
    .DELAY_VALUE (DELAY_VALUE_REG),
    .FDLY (FDLY_REG),
    .INIT (INIT_REG),
    .NATIVE_ODELAY_BYPASS (NATIVE_ODELAY_BYPASS_REG),
    .OUTPUT_PHASE_90 (OUTPUT_PHASE_90_REG),
    .REFCLK_FREQUENCY (REFCLK_FREQUENCY_BIN),
    .SIM_VERSION (SIM_VERSION_BIN),
    .UPDATE_MODE (UPDATE_MODE_REG),
    .BIT_CTRL_OUT (BIT_CTRL_OUT_out),
    .CDATAOUT (CDATAOUT_out),
    .CNTVALUEOUT (CNTVALUEOUT_out),
    .TRI_OUT (TRI_OUT_out),
    .BIT_CTRL_IN (BIT_CTRL_IN_in),
    .CDATAIN0 (CDATAIN0_in),
    .CDATAIN1 (CDATAIN1_in),
    .CE (CE_in),
    .CLK (CLK_in),
    .CNTVALUEIN (CNTVALUEIN_in),
    .EN_VTC (EN_VTC_in),
    .INC (INC_in),
    .LOAD (LOAD_in),
    .OFD_CE (OFD_CE_in),
    .RST (RST_in),
    .RST_DLY (RST_DLY_in),
    .GSR (glblGSR)
  );
end 
endgenerate

`ifdef XIL_TIMING
  reg notifier;
  
  wire clk_en_n;
  wire clk_en_p;
  
  assign clk_en_n =  IS_CLK_INVERTED_BIN;
  assign clk_en_p = ~IS_CLK_INVERTED_BIN;
`endif

  specify
    (CLK => CNTVALUEOUT[0]) = (100:100:100, 100:100:100);
    (CLK => CNTVALUEOUT[1]) = (100:100:100, 100:100:100);
    (CLK => CNTVALUEOUT[2]) = (100:100:100, 100:100:100);
    (CLK => CNTVALUEOUT[3]) = (100:100:100, 100:100:100);
    (CLK => CNTVALUEOUT[4]) = (100:100:100, 100:100:100);
    (CLK => CNTVALUEOUT[5]) = (100:100:100, 100:100:100);
    (CLK => CNTVALUEOUT[6]) = (100:100:100, 100:100:100);
    (CLK => CNTVALUEOUT[7]) = (100:100:100, 100:100:100);
    (CLK => CNTVALUEOUT[8]) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $period (negedge CLK, 0:0:0, notifier);
    $period (posedge CLK, 0:0:0, notifier);
    $setuphold (negedge CLK, negedge CE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CE_delay);
    $setuphold (negedge CLK, negedge CNTVALUEIN[0], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[0]);
    $setuphold (negedge CLK, negedge CNTVALUEIN[1], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[1]);
    $setuphold (negedge CLK, negedge CNTVALUEIN[2], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[2]);
    $setuphold (negedge CLK, negedge CNTVALUEIN[3], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[3]);
    $setuphold (negedge CLK, negedge CNTVALUEIN[4], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[4]);
    $setuphold (negedge CLK, negedge CNTVALUEIN[5], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[5]);
    $setuphold (negedge CLK, negedge CNTVALUEIN[6], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[6]);
    $setuphold (negedge CLK, negedge CNTVALUEIN[7], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[7]);
    $setuphold (negedge CLK, negedge CNTVALUEIN[8], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[8]);
    $setuphold (negedge CLK, negedge INC, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, INC_delay);
    $setuphold (negedge CLK, negedge LOAD, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, LOAD_delay);
    $setuphold (negedge CLK, posedge CE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CE_delay);
    $setuphold (negedge CLK, posedge CNTVALUEIN[0], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[0]);
    $setuphold (negedge CLK, posedge CNTVALUEIN[1], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[1]);
    $setuphold (negedge CLK, posedge CNTVALUEIN[2], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[2]);
    $setuphold (negedge CLK, posedge CNTVALUEIN[3], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[3]);
    $setuphold (negedge CLK, posedge CNTVALUEIN[4], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[4]);
    $setuphold (negedge CLK, posedge CNTVALUEIN[5], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[5]);
    $setuphold (negedge CLK, posedge CNTVALUEIN[6], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[6]);
    $setuphold (negedge CLK, posedge CNTVALUEIN[7], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[7]);
    $setuphold (negedge CLK, posedge CNTVALUEIN[8], 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay[8]);
    $setuphold (negedge CLK, posedge INC, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, INC_delay);
    $setuphold (negedge CLK, posedge LOAD, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, LOAD_delay);
    $setuphold (posedge CLK, negedge CE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CE_delay);
    $setuphold (posedge CLK, negedge CNTVALUEIN[0], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[0]);
    $setuphold (posedge CLK, negedge CNTVALUEIN[1], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[1]);
    $setuphold (posedge CLK, negedge CNTVALUEIN[2], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[2]);
    $setuphold (posedge CLK, negedge CNTVALUEIN[3], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[3]);
    $setuphold (posedge CLK, negedge CNTVALUEIN[4], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[4]);
    $setuphold (posedge CLK, negedge CNTVALUEIN[5], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[5]);
    $setuphold (posedge CLK, negedge CNTVALUEIN[6], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[6]);
    $setuphold (posedge CLK, negedge CNTVALUEIN[7], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[7]);
    $setuphold (posedge CLK, negedge CNTVALUEIN[8], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[8]);
    $setuphold (posedge CLK, negedge INC, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, INC_delay);
    $setuphold (posedge CLK, negedge LOAD, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, LOAD_delay);
    $setuphold (posedge CLK, posedge CE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CE_delay);
    $setuphold (posedge CLK, posedge CNTVALUEIN[0], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[0]);
    $setuphold (posedge CLK, posedge CNTVALUEIN[1], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[1]);
    $setuphold (posedge CLK, posedge CNTVALUEIN[2], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[2]);
    $setuphold (posedge CLK, posedge CNTVALUEIN[3], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[3]);
    $setuphold (posedge CLK, posedge CNTVALUEIN[4], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[4]);
    $setuphold (posedge CLK, posedge CNTVALUEIN[5], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[5]);
    $setuphold (posedge CLK, posedge CNTVALUEIN[6], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[6]);
    $setuphold (posedge CLK, posedge CNTVALUEIN[7], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[7]);
    $setuphold (posedge CLK, posedge CNTVALUEIN[8], 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay[8]);
    $setuphold (posedge CLK, posedge INC, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, INC_delay);
    $setuphold (posedge CLK, posedge LOAD, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, LOAD_delay);
    $width (negedge CLK, 0:0:0, 0, notifier);
    $width (posedge CLK, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
