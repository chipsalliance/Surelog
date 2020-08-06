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
//  /   /                        TX_BITSLICE
// /___/   /\      Filename    : TX_BITSLICE.v
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

module TX_BITSLICE #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter integer DATA_WIDTH = 8,
  parameter DELAY_FORMAT = "TIME",
  parameter DELAY_TYPE = "FIXED",
  parameter integer DELAY_VALUE = 0,
  parameter ENABLE_PRE_EMPHASIS = "FALSE",
  parameter [0:0] INIT = 1'b1,
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [0:0] IS_RST_DLY_INVERTED = 1'b0,
  parameter [0:0] IS_RST_INVERTED = 1'b0,
  parameter NATIVE_ODELAY_BYPASS = "FALSE",
  parameter OUTPUT_PHASE_90 = "FALSE",
  parameter real REFCLK_FREQUENCY = 300.0,
  parameter SIM_DEVICE = "ULTRASCALE",
  parameter real SIM_VERSION = 2.0,
  parameter TBYTE_CTL = "TBYTE_IN",
  parameter UPDATE_MODE = "ASYNC"
)(
  output [8:0] CNTVALUEOUT,
  output O,
  output [39:0] RX_BIT_CTRL_OUT,
  output [39:0] TX_BIT_CTRL_OUT,
  output T_OUT,

  input CE,
  input CLK,
  input [8:0] CNTVALUEIN,
  input [7:0] D,
  input EN_VTC,
  input INC,
  input LOAD,
  input RST,
  input RST_DLY,
  input [39:0] RX_BIT_CTRL_IN,
  input T,
  input TBYTE_IN,
  input [39:0] TX_BIT_CTRL_IN
);

// define constants
  localparam MODULE_NAME = "TX_BITSLICE";
  localparam in_delay    = 0;
  localparam out_delay   = 0;
  localparam inclk_delay    = 0;
  localparam outclk_delay   = 0;

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
  reg warning_flag = 1'b1;
`ifdef XIL_DR
  `include "TX_BITSLICE_dr.v"
`else
  localparam [31:0] DATA_WIDTH_REG = DATA_WIDTH;
  localparam [40:1] DELAY_FORMAT_REG = DELAY_FORMAT;
  localparam [64:1] DELAY_TYPE_REG = DELAY_TYPE;
  localparam [31:0] DELAY_VALUE_REG = DELAY_VALUE;
  localparam [40:1] ENABLE_PRE_EMPHASIS_REG = ENABLE_PRE_EMPHASIS;
  localparam [0:0] INIT_REG = INIT;
  localparam [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
  localparam [0:0] IS_RST_DLY_INVERTED_REG = IS_RST_DLY_INVERTED;
  localparam [0:0] IS_RST_INVERTED_REG = IS_RST_INVERTED;
  localparam [40:1] NATIVE_ODELAY_BYPASS_REG = NATIVE_ODELAY_BYPASS;
  localparam [40:1] OUTPUT_PHASE_90_REG = OUTPUT_PHASE_90;
  localparam real REFCLK_FREQUENCY_REG = REFCLK_FREQUENCY;
  localparam [152:1] SIM_DEVICE_REG = SIM_DEVICE;
  localparam real SIM_VERSION_REG = SIM_VERSION;
  localparam [64:1] TBYTE_CTL_REG = TBYTE_CTL;
  localparam [48:1] UPDATE_MODE_REG = UPDATE_MODE;
`endif

  localparam [0:0] DC_ADJ_EN_REG = 1'b0;
  localparam [2:0] FDLY_REG = 3'b010;
  localparam [5:0] SPARE_REG = 6'b000000;
  localparam [40:1] FIFO_ENABLE_REG = "TRUE";
  localparam [40:1] RX_Q4_ROUTETHRU_REG = "FALSE";
  localparam [40:1] RX_Q5_ROUTETHRU_REG = "FALSE";
  localparam [40:1] TX_Q_ROUTETHRU_REG = "FALSE";
  localparam [40:1] TX_T_OUT_ROUTETHRU_REG = "FALSE";
  localparam [40:1] XIPHY_BITSLICE_MODE_REG = "TRUE";
  localparam [40:1] RX_DELAY_FORMAT_REG = "COUNT";
  localparam [112:1] RX_DATA_TYPE_REG = "DATA_AND_CLOCK";
  

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

  wire O_out;
  wire T_OUT_out;
  wire [39:0] RX_BIT_CTRL_OUT_out;
  wire [39:0] TX_BIT_CTRL_OUT_out;
  wire [8:0] CNTVALUEOUT_out;

  wire O_delay;
  wire T_OUT_delay;
  wire [39:0] RX_BIT_CTRL_OUT_delay;
  wire [39:0] TX_BIT_CTRL_OUT_delay;
  wire [8:0] CNTVALUEOUT_delay;

  wire CE_in;
  wire CLK_in;
  wire EN_VTC_in;
  wire FIFO_RD_CLK_in;
  wire FIFO_RD_EN_in;
  wire IFD_CE_in;
  wire INC_in;
  wire LOAD_in;
  wire OFD_CE_in;
  wire RST_DLY_in;
  wire RST_in;
  wire RX_CE_in;
  wire RX_CLK_in;
  wire RX_DATAIN1_in;
  wire RX_EN_VTC_in;
  wire RX_INC_in;
  wire RX_LOAD_in;
  wire RX_RESET_in;
  wire RX_RST_in;
  wire TBYTE_IN_in;
  wire T_in;
  wire [39:0] RX_BIT_CTRL_IN_in;
  wire [39:0] TX_BIT_CTRL_IN_in;
  wire [7:0] D_in;
  wire [8:0] CNTVALUEIN_in;
  wire [8:0] RX_CNTVALUEIN_in;

  wire CE_delay;
  wire CLK_delay;
  wire EN_VTC_delay;
  wire INC_delay;
  wire LOAD_delay;
  wire RST_DLY_delay;
  wire RST_delay;
  wire TBYTE_IN_delay;
  wire T_delay;
  wire [39:0] RX_BIT_CTRL_IN_delay;
  wire [39:0] TX_BIT_CTRL_IN_delay;
  wire [7:0] D_delay;
  wire [8:0] CNTVALUEIN_delay;
  wire ODELAY_DATAIN0_out;
  wire ODELAY_DATAOUT_out;
  
  assign #(out_delay) CNTVALUEOUT = (EN_VTC_in ===  1'b1) ? 9'bxxxxxxxxx : CNTVALUEOUT_delay;
  assign #(out_delay) O = O_delay;
  assign #(out_delay) RX_BIT_CTRL_OUT = RX_BIT_CTRL_OUT_delay;
  assign #(out_delay) TX_BIT_CTRL_OUT = TX_BIT_CTRL_OUT_delay;
  assign #(out_delay) T_OUT = T_OUT_delay;

`ifdef XIL_TIMING
  reg notifier;
`endif

`ifndef XIL_TIMING // inputs with timing checks
  assign #(inclk_delay) CLK_delay = CLK;

  assign #(in_delay) CE_delay = CE;
  assign #(in_delay) CNTVALUEIN_delay = CNTVALUEIN;
  assign #(in_delay) D_delay = D;
  assign #(in_delay) INC_delay = INC;
  assign #(in_delay) LOAD_delay = LOAD;
  assign #(in_delay) TX_BIT_CTRL_IN_delay[25] = TX_BIT_CTRL_IN[25];  
  assign #(in_delay) TX_BIT_CTRL_IN_delay[26] = TX_BIT_CTRL_IN[26];  
`endif

// inputs with no timing checks
  assign #(in_delay) EN_VTC_delay = EN_VTC;
  assign #(in_delay) RST_DLY_delay = RST_DLY;
  assign #(in_delay) RST_delay = RST;
  assign #(in_delay) RX_BIT_CTRL_IN_delay = RX_BIT_CTRL_IN;
  assign #(in_delay) TBYTE_IN_delay = TBYTE_IN;
  assign #(in_delay) TX_BIT_CTRL_IN_delay[0] = TX_BIT_CTRL_IN[0];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[1] = TX_BIT_CTRL_IN[1];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[2] = TX_BIT_CTRL_IN[2];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[3] = TX_BIT_CTRL_IN[3];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[4] = TX_BIT_CTRL_IN[4];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[5] = TX_BIT_CTRL_IN[5];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[6] = TX_BIT_CTRL_IN[6];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[7] = TX_BIT_CTRL_IN[7];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[8] = TX_BIT_CTRL_IN[8];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[9] =  TX_BIT_CTRL_IN[9];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[10] = TX_BIT_CTRL_IN[10];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[11] = TX_BIT_CTRL_IN[11];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[12] = TX_BIT_CTRL_IN[12];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[13] = TX_BIT_CTRL_IN[13];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[14] = TX_BIT_CTRL_IN[14];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[15] = TX_BIT_CTRL_IN[15];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[16] = TX_BIT_CTRL_IN[16];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[17] = TX_BIT_CTRL_IN[17];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[18] = TX_BIT_CTRL_IN[18];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[19] = TX_BIT_CTRL_IN[19];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[20] = TX_BIT_CTRL_IN[20];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[21] = TX_BIT_CTRL_IN[21];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[22] = TX_BIT_CTRL_IN[22];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[23] = TX_BIT_CTRL_IN[23];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[24] = TX_BIT_CTRL_IN[24];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[27] = TX_BIT_CTRL_IN[27];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[28] = TX_BIT_CTRL_IN[28];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[29] = TX_BIT_CTRL_IN[29];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[30] = TX_BIT_CTRL_IN[30];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[31] = TX_BIT_CTRL_IN[31];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[32] = TX_BIT_CTRL_IN[32];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[33] = TX_BIT_CTRL_IN[33];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[34] = TX_BIT_CTRL_IN[34];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[35] = TX_BIT_CTRL_IN[35];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[36] = TX_BIT_CTRL_IN[36];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[37] = TX_BIT_CTRL_IN[37];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[38] = TX_BIT_CTRL_IN[38];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[39] = TX_BIT_CTRL_IN[39];
  assign #(in_delay) T_delay = T;

  assign CNTVALUEOUT_delay = CNTVALUEOUT_out;
  assign O_delay = O_out;
  assign RX_BIT_CTRL_OUT_delay = RX_BIT_CTRL_OUT_out;
  assign TX_BIT_CTRL_OUT_delay = TX_BIT_CTRL_OUT_out;
  assign T_OUT_delay = T_OUT_out;

  assign CE_in = CE_delay;
  assign CLK_in = CLK_delay ^ IS_CLK_INVERTED_BIN;
  assign CNTVALUEIN_in = CNTVALUEIN_delay;
  assign D_in = D_delay;
  assign EN_VTC_in = EN_VTC_delay;
  assign INC_in = INC_delay;
  assign LOAD_in = LOAD_delay;
  assign RST_DLY_in = RST_DLY_delay ^ IS_RST_DLY_INVERTED_BIN;
  assign RST_in = RST_delay ^ IS_RST_INVERTED_BIN;
  assign RX_BIT_CTRL_IN_in = RX_BIT_CTRL_IN_delay;
  assign TBYTE_IN_in = TBYTE_IN_delay;
  assign TX_BIT_CTRL_IN_in = TX_BIT_CTRL_IN_delay;
  assign T_in = T_delay;

  assign IS_CLK_INVERTED_BIN = IS_CLK_INVERTED_REG;
  
  assign IS_RST_DLY_INVERTED_BIN = IS_RST_DLY_INVERTED_REG;
  
  assign IS_RST_INVERTED_BIN = IS_RST_INVERTED_REG;
  
  assign REFCLK_FREQUENCY_BIN = REFCLK_FREQUENCY_REG * 1000;
  
  assign SIM_VERSION_BIN = SIM_VERSION_REG * 1000;
  
  initial begin
    #1;
    trig_attr = ~trig_attr;
  end

   always @(EN_VTC_in) begin
   if (EN_VTC_in ===0 && DELAY_FORMAT_REG == "TIME" && warning_flag === 1'b1 ) begin
     $display("Warning: [Unisim %s-1] BISC Calibration : DELAY_FORMAT set to TIME with EN_VTC signal set to 0. In hardware, when the EN_VTC signal is low during the initial calibration process, the BISC will never complete and the DLY_RDY and VTC_RDY status signals from the BITSLICE_CONTROL remain low. Simulation will not reflect this behavior. In simulation, the DLY_RDY and VTC_RDY from the BITSLICE_CONTROL will assert high. You should ensure the EN_VTC signal is held high during initial BISC self calibration to ensure BISC completes in hardware. See Select IO Userguide UG571 for more information.Instance: %m", MODULE_NAME);
     warning_flag = 1'b0;
   end
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
        ((ENABLE_PRE_EMPHASIS_REG != "FALSE") &&
         (ENABLE_PRE_EMPHASIS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-106] ENABLE_PRE_EMPHASIS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, ENABLE_PRE_EMPHASIS_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((NATIVE_ODELAY_BYPASS_REG != "FALSE") &&
         (NATIVE_ODELAY_BYPASS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-112] NATIVE_ODELAY_BYPASS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, NATIVE_ODELAY_BYPASS_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((OUTPUT_PHASE_90_REG != "FALSE") &&
         (OUTPUT_PHASE_90_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-113] OUTPUT_PHASE_90 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, OUTPUT_PHASE_90_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        (DELAY_FORMAT_REG != "COUNT" && SIM_DEVICE != "ULTRASCALE" && (REFCLK_FREQUENCY_REG < 300.0 || REFCLK_FREQUENCY_REG > 2667.0))) begin
      $display("Error: [Unisim %s-114] REFCLK_FREQUENCY attribute is set to %f.  Legal values for this attribute are 300.0 to 2667.0. Instance: %m", MODULE_NAME, REFCLK_FREQUENCY_REG);
      attr_err = 1'b1;
    end
    if ((attr_test == 1'b1) ||
        (DELAY_FORMAT_REG != "COUNT" && SIM_DEVICE == "ULTRASCALE" && (REFCLK_FREQUENCY_REG < 200.0 || REFCLK_FREQUENCY_REG > 2400.0))) begin
      $display("Error: [Unisim %s-114] REFCLK_FREQUENCY attribute is set to %f.  Legal values for this attribute are 200.0 to 2400.0. Instance: %m", MODULE_NAME, REFCLK_FREQUENCY_REG);
      attr_err = 1'b1;
    end
 
    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2"))) begin
      $display("Error: [Unisim %s-117] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE, ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1 or ULTRASCALE_PLUS_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
       ((SIM_VERSION_REG != 2.0) &&
        (SIM_VERSION_REG != 1.0))) begin
      $display("Error: [Unisim %s-118] SIM_VERSION attribute is set to %f.  Legal values for this attribute are 2.0 or 1.0. Instance: %m", MODULE_NAME, SIM_VERSION_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((TBYTE_CTL_REG != "TBYTE_IN") &&
         (TBYTE_CTL_REG != "T"))) begin
      $display("Error: [Unisim %s-119] TBYTE_CTL attribute is set to %s.  Legal values for this attribute are TBYTE_IN or T. Instance: %m", MODULE_NAME, TBYTE_CTL_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((UPDATE_MODE_REG != "ASYNC") &&
         (UPDATE_MODE_REG != "MANUAL") &&
         (UPDATE_MODE_REG != "SYNC"))) begin
      $display("Error: [Unisim %s-122] UPDATE_MODE attribute is set to %s.  Legal values for this attribute are ASYNC, MANUAL or SYNC. Instance: %m", MODULE_NAME, UPDATE_MODE_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end

  assign RX_CLK_in = 1'b1; // tie off

  assign FIFO_RD_CLK_in = 1'b0; // tie off
  assign FIFO_RD_EN_in = 1'b0; // tie off
  assign IFD_CE_in = 1'b0; // tie off
  assign OFD_CE_in = 1'b0; // tie off
  assign RX_CE_in = 1'b0; // tie off
  assign RX_CNTVALUEIN_in = 9'b000000000; // tie off
  assign RX_DATAIN1_in = 1'b0; // tie off
  assign RX_EN_VTC_in = 1'b1; // tie off
  assign RX_INC_in = 1'b0; // tie off
  assign RX_LOAD_in = 1'b0; // tie off
  assign RX_RESET_in = 1'b0; // tie off
  assign RX_RST_in = 1'b0; // tie off

generate
if ((SIM_DEVICE == "ULTRASCALE_PLUS") || (SIM_DEVICE == "ULTRASCALE_PLUS_ES1") || (SIM_DEVICE == "ULTRASCALE_PLUS_ES2")) begin : generate_block1
  SIP_TX_BITSLICE_D1 SIP_TX_BITSLICE_INST (
    .DATA_WIDTH (DATA_WIDTH_REG),
    .DC_ADJ_EN (DC_ADJ_EN_REG),
    .DELAY_FORMAT (DELAY_FORMAT_REG),
    .DELAY_TYPE (DELAY_TYPE_REG),
    .DELAY_VALUE (DELAY_VALUE_REG),
    .ENABLE_PRE_EMPHASIS (ENABLE_PRE_EMPHASIS_REG),
    .FIFO_ENABLE (FIFO_ENABLE_REG),
    .SPARE (SPARE_REG),
    .FDLY (FDLY_REG),
    .INIT (INIT_REG),
    .NATIVE_ODELAY_BYPASS (NATIVE_ODELAY_BYPASS_REG),
    .OUTPUT_PHASE_90 (OUTPUT_PHASE_90_REG),
    .REFCLK_FREQUENCY (REFCLK_FREQUENCY_BIN),
    .RX_DATA_TYPE (RX_DATA_TYPE_REG),
    .RX_DELAY_FORMAT (RX_DELAY_FORMAT_REG),
    .RX_Q4_ROUTETHRU (RX_Q4_ROUTETHRU_REG),
    .RX_Q5_ROUTETHRU (RX_Q5_ROUTETHRU_REG),
    .TBYTE_CTL (TBYTE_CTL_REG),
    .TX_Q_ROUTETHRU (TX_Q_ROUTETHRU_REG),
    .TX_T_OUT_ROUTETHRU (TX_T_OUT_ROUTETHRU_REG),
    .UPDATE_MODE (UPDATE_MODE_REG),
    .XIPHY_BITSLICE_MODE (XIPHY_BITSLICE_MODE_REG),
    .CNTVALUEOUT (CNTVALUEOUT_out),
    .O (O_out),
    .RX_BIT_CTRL_OUT (RX_BIT_CTRL_OUT_out),
    .TX_BIT_CTRL_OUT (TX_BIT_CTRL_OUT_out),
    .T_OUT (T_OUT_out),
    .CE (CE_in),
    .CLK (CLK_in),
    .CNTVALUEIN (CNTVALUEIN_in),
    .D (D_in),
    .EN_VTC (EN_VTC_in),
    .FIFO_RD_CLK (FIFO_RD_CLK_in),
    .FIFO_RD_EN (FIFO_RD_EN_in),
    .IFD_CE (IFD_CE_in),
    .INC (INC_in),
    .LOAD (LOAD_in),
    .OFD_CE (OFD_CE_in),
    .RST (RST_in),
    .RST_DLY (RST_DLY_in),
    .RX_BIT_CTRL_IN (RX_BIT_CTRL_IN_in),
    .RX_CE (RX_CE_in),
    .RX_CLK (RX_CLK_in),
    .RX_CNTVALUEIN (RX_CNTVALUEIN_in),
    .RX_DATAIN1 (RX_DATAIN1_in),
    .RX_EN_VTC (RX_EN_VTC_in),
    .RX_INC (RX_INC_in),
    .RX_LOAD (RX_LOAD_in),
    .RX_RESET (RX_RESET_in),
    .RX_RST (RX_RST_in),
    .T (T_in),
    .TBYTE_IN (TBYTE_IN_in),
    .TX_BIT_CTRL_IN (TX_BIT_CTRL_IN_in),
    .SIM_ODELAY_DATAIN0(ODELAY_DATAIN0_out),
    .SIM_ODELAY_DATAOUT(ODELAY_DATAOUT_out),
    .GSR (glblGSR)
  );
end else if (SIM_DEVICE == "ULTRASCALE") begin : generate_block1
  SIP_TX_BITSLICE_K2 SIP_TX_BITSLICE_INST (
    .DATA_WIDTH (DATA_WIDTH_REG),
    .DC_ADJ_EN (DC_ADJ_EN_REG),
    .DELAY_FORMAT (DELAY_FORMAT_REG),
    .DELAY_TYPE (DELAY_TYPE_REG),
    .DELAY_VALUE (DELAY_VALUE_REG),
    .ENABLE_PRE_EMPHASIS (ENABLE_PRE_EMPHASIS_REG),
    .FDLY (FDLY_REG),
    .INIT (INIT_REG),
    .NATIVE_ODELAY_BYPASS (NATIVE_ODELAY_BYPASS_REG),
    .OUTPUT_PHASE_90 (OUTPUT_PHASE_90_REG),
    .REFCLK_FREQUENCY (REFCLK_FREQUENCY_BIN),
    .RX_DATA_TYPE (RX_DATA_TYPE_REG),
    .RX_DELAY_FORMAT (RX_DELAY_FORMAT_REG),
    .RX_Q4_ROUTETHRU (RX_Q4_ROUTETHRU_REG),
    .RX_Q5_ROUTETHRU (RX_Q5_ROUTETHRU_REG),
    .SIM_VERSION (SIM_VERSION_BIN),
    .TBYTE_CTL (TBYTE_CTL_REG),
    .TX_Q_ROUTETHRU (TX_Q_ROUTETHRU_REG),
    .TX_T_OUT_ROUTETHRU (TX_T_OUT_ROUTETHRU_REG),
    .UPDATE_MODE (UPDATE_MODE_REG),
    .XIPHY_BITSLICE_MODE (XIPHY_BITSLICE_MODE_REG),
    .CNTVALUEOUT (CNTVALUEOUT_out),
    .O (O_out),
    .RX_BIT_CTRL_OUT (RX_BIT_CTRL_OUT_out),
    .TX_BIT_CTRL_OUT (TX_BIT_CTRL_OUT_out),
    .T_OUT (T_OUT_out),
    .CE (CE_in),
    .CLK (CLK_in),
    .CNTVALUEIN (CNTVALUEIN_in),
    .D (D_in),
    .EN_VTC (EN_VTC_in),
    .FIFO_RD_CLK (FIFO_RD_CLK_in),
    .FIFO_RD_EN (FIFO_RD_EN_in),
    .IFD_CE (IFD_CE_in),
    .INC (INC_in),
    .LOAD (LOAD_in),
    .OFD_CE (OFD_CE_in),
    .RST (RST_in),
    .RST_DLY (RST_DLY_in),
    .RX_BIT_CTRL_IN (RX_BIT_CTRL_IN_in),
    .RX_CE (RX_CE_in),
    .RX_CLK (RX_CLK_in),
    .RX_CNTVALUEIN (RX_CNTVALUEIN_in),
    .RX_DATAIN1 (RX_DATAIN1_in),
    .RX_EN_VTC (RX_EN_VTC_in),
    .RX_INC (RX_INC_in),
    .RX_LOAD (RX_LOAD_in),
    .RX_RESET (RX_RESET_in),
    .RX_RST (RX_RST_in),
    .T (T_in),
    .TBYTE_IN (TBYTE_IN_in),
    .TX_BIT_CTRL_IN (TX_BIT_CTRL_IN_in),
    .SIM_ODELAY_DATAIN0(ODELAY_DATAIN0_out),
    .SIM_ODELAY_DATAOUT(ODELAY_DATAOUT_out),
    .GSR (glblGSR)
  );
end
endgenerate

`ifdef XIL_TIMING
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
    (D[0] => O) = (0:0:0, 0:0:0);
    (D[1] => T_OUT) = (0:0:0, 0:0:0);
`ifdef XIL_TIMING
    $period (negedge CLK, 0:0:0, notifier);
    $period (negedge TX_BIT_CTRL_IN[25], 0:0:0, notifier);
    $period (negedge TX_BIT_CTRL_IN[26], 0:0:0, notifier);
    $period (posedge CLK, 0:0:0, notifier);
    $period (posedge TX_BIT_CTRL_IN[25], 0:0:0, notifier);
    $period (posedge TX_BIT_CTRL_IN[26], 0:0:0, notifier);
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
    $setuphold (negedge TX_BIT_CTRL_IN[25], negedge D[0], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[0]);
    $setuphold (negedge TX_BIT_CTRL_IN[25], negedge D[1], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[1]);
    $setuphold (negedge TX_BIT_CTRL_IN[25], negedge D[2], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[2]);
    $setuphold (negedge TX_BIT_CTRL_IN[25], negedge D[3], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[3]);
    $setuphold (negedge TX_BIT_CTRL_IN[25], posedge D[0], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[0]);
    $setuphold (negedge TX_BIT_CTRL_IN[25], posedge D[1], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[1]);
    $setuphold (negedge TX_BIT_CTRL_IN[25], posedge D[2], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[2]);
    $setuphold (negedge TX_BIT_CTRL_IN[25], posedge D[3], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[3]);
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
    $setuphold (posedge TX_BIT_CTRL_IN[26], negedge D[0], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[0]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], negedge D[1], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[1]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], negedge D[2], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[2]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], negedge D[3], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[3]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], negedge D[4], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[4]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], negedge D[5], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[5]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], negedge D[6], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[6]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], negedge D[7], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[7]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], posedge D[0], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[0]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], posedge D[1], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[1]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], posedge D[2], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[2]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], posedge D[3], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[3]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], posedge D[4], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[4]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], posedge D[5], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[5]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], posedge D[6], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[6]);
    $setuphold (posedge TX_BIT_CTRL_IN[26], posedge D[7], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[26], D_delay[7]);
    $width (negedge CLK, 0:0:0, 0, notifier);
    $width (negedge TX_BIT_CTRL_IN[25], 0:0:0, 0, notifier);
    $width (negedge TX_BIT_CTRL_IN[26], 0:0:0, 0, notifier);
    $width (posedge CLK, 0:0:0, 0, notifier);
    $width (posedge TX_BIT_CTRL_IN[25], 0:0:0, 0, notifier);
    $width (posedge TX_BIT_CTRL_IN[26], 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
