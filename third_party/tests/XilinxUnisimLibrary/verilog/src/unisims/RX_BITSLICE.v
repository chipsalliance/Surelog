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
//  /   /                        RX_BITSLICE
// /___/   /\      Filename    : RX_BITSLICE.v
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

module RX_BITSLICE #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter CASCADE = "FALSE",
  parameter DATA_TYPE = "DATA",
  parameter integer DATA_WIDTH = 8,
  parameter DELAY_FORMAT = "TIME",
  parameter DELAY_TYPE = "FIXED",
  parameter integer DELAY_VALUE = 0,
  parameter integer DELAY_VALUE_EXT = 0,
  parameter FIFO_SYNC_MODE = "FALSE",
  parameter [0:0] IS_CLK_EXT_INVERTED = 1'b0,
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [0:0] IS_RST_DLY_EXT_INVERTED = 1'b0,
  parameter [0:0] IS_RST_DLY_INVERTED = 1'b0,
  parameter [0:0] IS_RST_INVERTED = 1'b0,
  parameter real REFCLK_FREQUENCY = 300.0,
  parameter SIM_DEVICE = "ULTRASCALE",
  parameter real SIM_VERSION = 2.0,
  parameter UPDATE_MODE = "ASYNC",
  parameter UPDATE_MODE_EXT = "ASYNC"
)(
  output [8:0] CNTVALUEOUT,
  output [8:0] CNTVALUEOUT_EXT,
  output FIFO_EMPTY,
  output FIFO_WRCLK_OUT,
  output [7:0] Q,
  output [39:0] RX_BIT_CTRL_OUT,
  output [39:0] TX_BIT_CTRL_OUT,

  input CE,
  input CE_EXT,
  input CLK,
  input CLK_EXT,
  input [8:0] CNTVALUEIN,
  input [8:0] CNTVALUEIN_EXT,
  input DATAIN,
  input EN_VTC,
  input EN_VTC_EXT,
  input FIFO_RD_CLK,
  input FIFO_RD_EN,
  input INC,
  input INC_EXT,
  input LOAD,
  input LOAD_EXT,
  input RST,
  input RST_DLY,
  input RST_DLY_EXT,
  input [39:0] RX_BIT_CTRL_IN,
  input [39:0] TX_BIT_CTRL_IN
);

// define constants
  localparam MODULE_NAME = "RX_BITSLICE";
  localparam in_delay    = 0;
  localparam out_delay   = 0;
  localparam inclk_delay    = 0;
  localparam outclk_delay   = 0;

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
  reg warning_flag = 1'b1;
`ifdef XIL_DR
  `include "RX_BITSLICE_dr.v"
`else
  localparam [40:1] CASCADE_REG = CASCADE;
  localparam [112:1] DATA_TYPE_REG = DATA_TYPE;
  localparam [31:0] DATA_WIDTH_REG = DATA_WIDTH;
  localparam [40:1] DELAY_FORMAT_REG = DELAY_FORMAT;
  localparam [64:1] DELAY_TYPE_REG = DELAY_TYPE;
  localparam [31:0] DELAY_VALUE_REG = DELAY_VALUE;
  localparam [31:0] DELAY_VALUE_EXT_REG = DELAY_VALUE_EXT;
  localparam [40:1] FIFO_SYNC_MODE_REG = FIFO_SYNC_MODE;
  localparam [0:0] IS_CLK_EXT_INVERTED_REG = IS_CLK_EXT_INVERTED;
  localparam [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
  localparam [0:0] IS_RST_DLY_EXT_INVERTED_REG = IS_RST_DLY_EXT_INVERTED;
  localparam [0:0] IS_RST_DLY_INVERTED_REG = IS_RST_DLY_INVERTED;
  localparam [0:0] IS_RST_INVERTED_REG = IS_RST_INVERTED;
  localparam real REFCLK_FREQUENCY_REG = REFCLK_FREQUENCY;
  localparam [152:1] SIM_DEVICE_REG = SIM_DEVICE;
  localparam real SIM_VERSION_REG = SIM_VERSION;
  localparam [48:1] UPDATE_MODE_REG = UPDATE_MODE;
  localparam [48:1] UPDATE_MODE_EXT_REG = UPDATE_MODE_EXT;
`endif

  localparam [0:0] DC_ADJ_EN_REG = 1'b0;
  localparam [0:0] DC_ADJ_EN_EXT_REG = 1'b0;
  localparam [40:1] DDR_DIS_DQS_REG = "TRUE";
  localparam [40:1] FIFO_ENABLE_REG = "TRUE";
  localparam [5:0] SPARE_REG = 6'b000000;
  localparam [2:0] FDLY_REG = 3'b010;
  localparam [2:0] FDLY_EXT_REG = 3'b010;
  localparam [40:1] RX_Q4_ROUTETHRU_REG = "FALSE";
  localparam [40:1] RX_Q5_ROUTETHRU_REG = "FALSE";
  localparam [64:1] TBYTE_CTL_REG = "T";
  localparam [40:1] TX_Q_ROUTETHRU_REG = "FALSE";
  localparam [40:1] TX_T_OUT_ROUTETHRU_REG = "FALSE";
  localparam [40:1] XIPHY_BITSLICE_MODE_REG = "TRUE";

  wire IS_CLK_EXT_INVERTED_BIN;
  wire IS_CLK_INVERTED_BIN;
  wire IS_RST_DLY_EXT_INVERTED_BIN;
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

  wire FIFO_EMPTY_out;
  wire FIFO_WRCLK_OUT_out;
  wire [39:0] RX_BIT_CTRL_OUT_out;
  wire [39:0] TX_BIT_CTRL_OUT_out;
  wire [7:0] Q_out;
  wire [8:0] CNTVALUEOUT_EXT_out;
  wire [8:0] CNTVALUEOUT_out;

  wire FIFO_EMPTY_delay;
  wire FIFO_WRCLK_OUT_delay;
  wire [39:0] RX_BIT_CTRL_OUT_delay;
  wire [39:0] TX_BIT_CTRL_OUT_delay;
  wire [7:0] Q_delay;
  wire [8:0] CNTVALUEOUT_EXT_delay;
  wire [8:0] CNTVALUEOUT_delay;

  wire CE_EXT_in;
  wire CE_in;
  wire CLK_EXT_in;
  wire CLK_in;
  wire DATAIN_in;
  wire EN_VTC_EXT_in;
  wire EN_VTC_in;
  wire FIFO_RD_CLK_in;
  wire FIFO_RD_EN_in;
  wire IFD_CE_in;
  wire INC_EXT_in;
  wire INC_in;
  wire LOAD_EXT_in;
  wire LOAD_in;
  wire OFD_CE_in;
  wire RST_DLY_EXT_in;
  wire RST_DLY_in;
  wire RST_in;
  wire RX_DATAIN1_in;
  wire TX_RST_in;
  wire T_in;
  wire [39:0] RX_BIT_CTRL_IN_in;
  wire [39:0] TX_BIT_CTRL_IN_in;
  wire [7:0] TX_D_in;
  wire [8:0] CNTVALUEIN_EXT_in;
  wire [8:0] CNTVALUEIN_in;

  wire CE_EXT_delay;
  wire CE_delay;
  wire CLK_EXT_delay;
  wire CLK_delay;
  wire DATAIN_delay;
  wire EN_VTC_EXT_delay;
  wire EN_VTC_delay;
  wire FIFO_RD_CLK_delay;
  wire FIFO_RD_EN_delay;
  wire INC_EXT_delay;
  wire INC_delay;
  wire LOAD_EXT_delay;
  wire LOAD_delay;
  wire RST_DLY_EXT_delay;
  wire RST_DLY_delay;
  wire RST_delay;
  wire [39:0] RX_BIT_CTRL_IN_delay;
  wire [39:0] TX_BIT_CTRL_IN_delay;
  wire [8:0] CNTVALUEIN_EXT_delay;
  wire [8:0] CNTVALUEIN_delay;
  wire IDELAY_DATAIN0_out;
  wire IDELAY_DATAOUT_out;


  assign #(out_delay) CNTVALUEOUT = (EN_VTC_in ===  1'b1) ? 9'bxxxxxxxxx : CNTVALUEOUT_delay;
  assign #(out_delay) CNTVALUEOUT_EXT = CNTVALUEOUT_EXT_delay;
  assign #(out_delay) FIFO_EMPTY = FIFO_EMPTY_delay;
  assign #(out_delay) FIFO_WRCLK_OUT = FIFO_WRCLK_OUT_delay;
  assign #(out_delay) Q = Q_delay;
  assign #(out_delay) RX_BIT_CTRL_OUT = RX_BIT_CTRL_OUT_delay;
  assign #(out_delay) TX_BIT_CTRL_OUT = TX_BIT_CTRL_OUT_delay;

`ifdef XIL_TIMING
  reg notifier;
`endif
`ifndef XIL_TIMING // inputs with timing checks
  assign #(inclk_delay) CLK_EXT_delay = CLK_EXT;
  assign #(inclk_delay) CLK_delay = CLK;

  assign #(in_delay) CE_EXT_delay = CE_EXT;
  assign #(in_delay) CE_delay = CE;
  assign #(in_delay) CNTVALUEIN_EXT_delay = CNTVALUEIN_EXT;
  assign #(in_delay) CNTVALUEIN_delay = CNTVALUEIN;
  assign #(in_delay) FIFO_RD_EN_delay = FIFO_RD_EN;
  assign #(in_delay) FIFO_RD_CLK_delay = FIFO_RD_CLK;
  assign #(in_delay) INC_EXT_delay = INC_EXT;
  assign #(in_delay) INC_delay = INC;
  assign #(in_delay) LOAD_EXT_delay = LOAD_EXT;
  assign #(in_delay) LOAD_delay = LOAD;
`endif

// inputs with no timing checks
  assign #(in_delay) DATAIN_delay = DATAIN;
  assign #(in_delay) EN_VTC_EXT_delay = EN_VTC_EXT;
  assign #(in_delay) EN_VTC_delay = EN_VTC;
  assign #(in_delay) RST_DLY_EXT_delay = RST_DLY_EXT;
  assign #(in_delay) RST_DLY_delay = RST_DLY;
  assign #(in_delay) RST_delay = RST;
  assign #(in_delay) RX_BIT_CTRL_IN_delay = RX_BIT_CTRL_IN;
  assign #(in_delay) TX_BIT_CTRL_IN_delay = TX_BIT_CTRL_IN;

  assign CNTVALUEOUT_EXT_delay = CNTVALUEOUT_EXT_out;
  assign CNTVALUEOUT_delay = CNTVALUEOUT_out;
  assign FIFO_EMPTY_delay = FIFO_EMPTY_out;
  assign FIFO_WRCLK_OUT_delay = FIFO_WRCLK_OUT_out;
  assign Q_delay = Q_out;
  assign RX_BIT_CTRL_OUT_delay = RX_BIT_CTRL_OUT_out;
  assign TX_BIT_CTRL_OUT_delay = TX_BIT_CTRL_OUT_out;

  assign CE_EXT_in = CE_EXT_delay;
  assign CE_in = CE_delay;
  assign CLK_EXT_in = CLK_EXT_delay ^ IS_CLK_EXT_INVERTED_BIN;
  assign CLK_in = CLK_delay ^ IS_CLK_INVERTED_BIN;
  assign CNTVALUEIN_EXT_in = CNTVALUEIN_EXT_delay;
  assign CNTVALUEIN_in = CNTVALUEIN_delay;
  assign DATAIN_in = DATAIN_delay;
  assign EN_VTC_EXT_in = EN_VTC_EXT_delay;
  assign EN_VTC_in = EN_VTC_delay;
  assign FIFO_RD_CLK_in = FIFO_RD_CLK_delay;
  assign FIFO_RD_EN_in = FIFO_RD_EN_delay;
  assign INC_EXT_in = INC_EXT_delay;
  assign INC_in = INC_delay;
  assign LOAD_EXT_in = LOAD_EXT_delay;
  assign LOAD_in = LOAD_delay;
  assign RST_DLY_EXT_in = RST_DLY_EXT_delay ^ IS_RST_DLY_EXT_INVERTED_BIN;
  assign RST_DLY_in = RST_DLY_delay ^ IS_RST_DLY_INVERTED_BIN;
  assign RST_in = RST_delay ^ IS_RST_INVERTED_BIN;
  assign RX_BIT_CTRL_IN_in = RX_BIT_CTRL_IN_delay;
  assign TX_BIT_CTRL_IN_in = TX_BIT_CTRL_IN_delay;

  assign IS_CLK_EXT_INVERTED_BIN = IS_CLK_EXT_INVERTED_REG;
  
  assign IS_CLK_INVERTED_BIN = IS_CLK_INVERTED_REG;
  
  assign IS_RST_DLY_EXT_INVERTED_BIN = IS_RST_DLY_EXT_INVERTED_REG;
  
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
        ((CASCADE_REG != "FALSE") &&
         (CASCADE_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-101] CASCADE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CASCADE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((DATA_TYPE_REG != "DATA") &&
         (DATA_TYPE_REG != "CLOCK") &&
         (DATA_TYPE_REG != "DATA_AND_CLOCK") &&
         (DATA_TYPE_REG != "SERIAL"))) begin
      $display("Error: [Unisim %s-102] DATA_TYPE attribute is set to %s.  Legal values for this attribute are DATA, CLOCK, DATA_AND_CLOCK or SERIAL. Instance: %m", MODULE_NAME, DATA_TYPE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((DATA_WIDTH_REG != 8) &&
         (DATA_WIDTH_REG != 4))) begin
      $display("Error: [Unisim %s-103] DATA_WIDTH attribute is set to %d.  Legal values for this attribute are 8 or 4. Instance: %m", MODULE_NAME, DATA_WIDTH_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((DELAY_FORMAT_REG != "TIME") &&
         (DELAY_FORMAT_REG != "COUNT"))) begin
      $display("Error: [Unisim %s-107] DELAY_FORMAT attribute is set to %s.  Legal values for this attribute are TIME or COUNT. Instance: %m", MODULE_NAME, DELAY_FORMAT_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((DELAY_TYPE_REG != "FIXED") &&
         (DELAY_TYPE_REG != "VAR_LOAD") &&
         (DELAY_TYPE_REG != "VARIABLE"))) begin
      $display("Error: [Unisim %s-108] DELAY_TYPE attribute is set to %s.  Legal values for this attribute are FIXED, VAR_LOAD or VARIABLE. Instance: %m", MODULE_NAME, DELAY_TYPE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        (SIM_DEVICE_REG == "ULTRASCALE" && ((DELAY_VALUE_REG < 0) || (DELAY_VALUE_REG > 1250)))) begin
      $display("Error: [Unisim %s-109] DELAY_VALUE attribute is set to %d.  Legal values for this attribute are 0 to 1250. Instance: %m", MODULE_NAME, DELAY_VALUE_REG);
      attr_err = 1'b1;
    end
    if ((attr_test == 1'b1) ||
        (SIM_DEVICE_REG != "ULTRASCALE" && ((DELAY_VALUE_REG < 0) || (DELAY_VALUE_REG > 1100)))) begin
      $display("Error: [Unisim %s-109] DELAY_VALUE attribute is set to %d.  Legal values for this attribute are 0 to 1100. Instance: %m", MODULE_NAME, DELAY_VALUE_REG);
      attr_err = 1'b1;
    end


    if ((attr_test == 1'b1) ||
        (SIM_DEVICE_REG == "ULTRASCALE" && ((DELAY_VALUE_EXT_REG < 0) || (DELAY_VALUE_EXT_REG > 1250)))) begin
      $display("Error: [Unisim %s-110] DELAY_VALUE_EXT attribute is set to %d.  Legal values for this attribute are 0 to 1250. Instance: %m", MODULE_NAME, DELAY_VALUE_EXT_REG);
      attr_err = 1'b1;
    end
    if ((attr_test == 1'b1) ||
        (SIM_DEVICE_REG != "ULTRASCALE" && ((DELAY_VALUE_EXT_REG < 0) || (DELAY_VALUE_EXT_REG > 1100)))) begin
      $display("Error: [Unisim %s-110] DELAY_VALUE_EXT attribute is set to %d.  Legal values for this attribute are 0 to 1100. Instance: %m", MODULE_NAME, DELAY_VALUE_EXT_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((FIFO_SYNC_MODE_REG != "FALSE") &&
         (FIFO_SYNC_MODE_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-113] FIFO_SYNC_MODE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, FIFO_SYNC_MODE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        (DELAY_FORMAT_REG != "COUNT" && SIM_DEVICE_REG != "ULTRASCALE" && (REFCLK_FREQUENCY_REG < 300.0 || REFCLK_FREQUENCY_REG > 2667.0))) begin
      $display("Error: [Unisim %s-119] REFCLK_FREQUENCY attribute is set to %f.  Legal values for this attribute are 300.0 to 2667.0. Instance: %m", MODULE_NAME, REFCLK_FREQUENCY_REG);
      attr_err = 1'b1;
    end
    if ((attr_test == 1'b1) ||
        (DELAY_FORMAT_REG != "COUNT" && SIM_DEVICE_REG == "ULTRASCALE" && (REFCLK_FREQUENCY_REG < 200.0 || REFCLK_FREQUENCY_REG > 2400.0))) begin
      $display("Error: [Unisim %s-119] REFCLK_FREQUENCY attribute is set to %f.  Legal values for this attribute are 200.0 to 2400.0. Instance: %m", MODULE_NAME, REFCLK_FREQUENCY_REG);
      attr_err = 1'b1;
    end
    
    
    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2"))) begin
      $display("Error: [Unisim %s-122] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE, ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1 or ULTRASCALE_PLUS_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
       ((SIM_VERSION_REG != 2.0) &&
        (SIM_VERSION_REG != 1.0))) begin
      $display("Error: [Unisim %s-123] SIM_VERSION attribute is set to %f.  Legal values for this attribute are 2.0 or 1.0. Instance: %m", MODULE_NAME, SIM_VERSION_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((UPDATE_MODE_REG != "ASYNC") &&
         (UPDATE_MODE_REG != "MANUAL") &&
         (UPDATE_MODE_REG != "SYNC"))) begin
      $display("Error: [Unisim %s-127] UPDATE_MODE attribute is set to %s.  Legal values for this attribute are ASYNC, MANUAL or SYNC. Instance: %m", MODULE_NAME, UPDATE_MODE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((UPDATE_MODE_EXT_REG != "ASYNC") &&
         (UPDATE_MODE_EXT_REG != "MANUAL") &&
         (UPDATE_MODE_EXT_REG != "SYNC"))) begin
      $display("Error: [Unisim %s-128] UPDATE_MODE_EXT attribute is set to %s.  Legal values for this attribute are ASYNC, MANUAL or SYNC. Instance: %m", MODULE_NAME, UPDATE_MODE_EXT_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end


  assign IFD_CE_in = 1'b0; // tie off
  assign OFD_CE_in = 1'b0; // tie off
  assign RX_DATAIN1_in = 1'b0; // tie off
  assign TX_D_in = 8'b00000000; // tie off
  assign TX_RST_in = 1'b0; // tie off
  assign T_in = 1'b1; // tie off

generate
if ((SIM_DEVICE == "ULTRASCALE_PLUS") || (SIM_DEVICE == "ULTRASCALE_PLUS_ES1") || (SIM_DEVICE == "ULTRASCALE_PLUS_ES2")) begin : generate_block1
  SIP_RX_BITSLICE_D1 SIP_RX_BITSLICE_INST (
    .CASCADE (CASCADE_REG),
    .DATA_TYPE (DATA_TYPE_REG),
    .DATA_WIDTH (DATA_WIDTH_REG),
    .DC_ADJ_EN (DC_ADJ_EN_REG),
    .DC_ADJ_EN_EXT (DC_ADJ_EN_EXT_REG),
    .DDR_DIS_DQS (DDR_DIS_DQS_REG),
    .DELAY_FORMAT (DELAY_FORMAT_REG),
    .DELAY_TYPE (DELAY_TYPE_REG),
    .DELAY_VALUE (DELAY_VALUE_REG),
    .DELAY_VALUE_EXT (DELAY_VALUE_EXT_REG),
    .FDLY (FDLY_REG),
    .FDLY_EXT (FDLY_EXT_REG),
    .FIFO_SYNC_MODE (FIFO_SYNC_MODE_REG),
    .REFCLK_FREQUENCY (REFCLK_FREQUENCY_BIN),
    .RX_Q4_ROUTETHRU (RX_Q4_ROUTETHRU_REG),
    .RX_Q5_ROUTETHRU (RX_Q5_ROUTETHRU_REG),
    .TBYTE_CTL (TBYTE_CTL_REG),
    .TX_Q_ROUTETHRU (TX_Q_ROUTETHRU_REG),
    .TX_T_OUT_ROUTETHRU (TX_T_OUT_ROUTETHRU_REG),
    .UPDATE_MODE (UPDATE_MODE_REG),
    .UPDATE_MODE_EXT (UPDATE_MODE_EXT_REG),
    .XIPHY_BITSLICE_MODE (XIPHY_BITSLICE_MODE_REG),
    .CNTVALUEOUT (CNTVALUEOUT_out),
    .CNTVALUEOUT_EXT (CNTVALUEOUT_EXT_out),
    .FIFO_EMPTY (FIFO_EMPTY_out),
    .FIFO_WRCLK_OUT (FIFO_WRCLK_OUT_out),
    .Q (Q_out),
    .RX_BIT_CTRL_OUT (RX_BIT_CTRL_OUT_out),
    .TX_BIT_CTRL_OUT (TX_BIT_CTRL_OUT_out),
    .CE (CE_in),
    .CE_EXT (CE_EXT_in),
    .CLK (CLK_in),
    .CLK_EXT (CLK_EXT_in),
    .CNTVALUEIN (CNTVALUEIN_in),
    .CNTVALUEIN_EXT (CNTVALUEIN_EXT_in),
    .DATAIN (DATAIN_in),
    .EN_VTC (EN_VTC_in),
    .EN_VTC_EXT (EN_VTC_EXT_in),
    .FIFO_RD_CLK (FIFO_RD_CLK_in),
    .FIFO_RD_EN (FIFO_RD_EN_in),
    .IFD_CE (IFD_CE_in),
    .INC (INC_in),
    .INC_EXT (INC_EXT_in),
    .LOAD (LOAD_in),
    .LOAD_EXT (LOAD_EXT_in),
    .OFD_CE (OFD_CE_in),
    .RST (RST_in),
    .RST_DLY (RST_DLY_in),
    .RST_DLY_EXT (RST_DLY_EXT_in),
    .RX_BIT_CTRL_IN (RX_BIT_CTRL_IN_in),
    .RX_DATAIN1 (RX_DATAIN1_in),
    .T (T_in),
    .TX_BIT_CTRL_IN (TX_BIT_CTRL_IN_in),
    .TX_D (TX_D_in),
    .TX_RST (TX_RST_in),
    .SIM_IDELAY_DATAIN0(IDELAY_DATAIN0_out),
    .SIM_IDELAY_DATAOUT(IDELAY_DATAOUT_out),
    .SPARE(SPARE_REG),
    .FIFO_ENABLE(FIFO_ENABLE_REG),
    .GSR (glblGSR)
  );
end else if (SIM_DEVICE == "ULTRASCALE") begin : generate_block1
  SIP_RX_BITSLICE_K2 SIP_RX_BITSLICE_INST (
    .CASCADE (CASCADE_REG),
    .DATA_TYPE (DATA_TYPE_REG),
    .DATA_WIDTH (DATA_WIDTH_REG),
    .DC_ADJ_EN (DC_ADJ_EN_REG),
    .DC_ADJ_EN_EXT (DC_ADJ_EN_EXT_REG),
    .DDR_DIS_DQS (DDR_DIS_DQS_REG),
    .DELAY_FORMAT (DELAY_FORMAT_REG),
    .DELAY_TYPE (DELAY_TYPE_REG),
    .DELAY_VALUE (DELAY_VALUE_REG),
    .DELAY_VALUE_EXT (DELAY_VALUE_EXT_REG),
    .FDLY (FDLY_REG),
    .FDLY_EXT (FDLY_EXT_REG),
    .FIFO_SYNC_MODE (FIFO_SYNC_MODE_REG),
    .REFCLK_FREQUENCY (REFCLK_FREQUENCY_BIN),
    .RX_Q4_ROUTETHRU (RX_Q4_ROUTETHRU_REG),
    .RX_Q5_ROUTETHRU (RX_Q5_ROUTETHRU_REG),
    .SIM_VERSION (SIM_VERSION_BIN),
    .TBYTE_CTL (TBYTE_CTL_REG),
    .TX_Q_ROUTETHRU (TX_Q_ROUTETHRU_REG),
    .TX_T_OUT_ROUTETHRU (TX_T_OUT_ROUTETHRU_REG),
    .UPDATE_MODE (UPDATE_MODE_REG),
    .UPDATE_MODE_EXT (UPDATE_MODE_EXT_REG),
    .XIPHY_BITSLICE_MODE (XIPHY_BITSLICE_MODE_REG),
    .CNTVALUEOUT (CNTVALUEOUT_out),
    .CNTVALUEOUT_EXT (CNTVALUEOUT_EXT_out),
    .FIFO_EMPTY (FIFO_EMPTY_out),
    .FIFO_WRCLK_OUT (FIFO_WRCLK_OUT_out),
    .Q (Q_out),
    .RX_BIT_CTRL_OUT (RX_BIT_CTRL_OUT_out),
    .TX_BIT_CTRL_OUT (TX_BIT_CTRL_OUT_out),
    .CE (CE_in),
    .CE_EXT (CE_EXT_in),
    .CLK (CLK_in),
    .CLK_EXT (CLK_EXT_in),
    .CNTVALUEIN (CNTVALUEIN_in),
    .CNTVALUEIN_EXT (CNTVALUEIN_EXT_in),
    .DATAIN (DATAIN_in),
    .EN_VTC (EN_VTC_in),
    .EN_VTC_EXT (EN_VTC_EXT_in),
    .FIFO_RD_CLK (FIFO_RD_CLK_in),
    .FIFO_RD_EN (FIFO_RD_EN_in),
    .IFD_CE (IFD_CE_in),
    .INC (INC_in),
    .INC_EXT (INC_EXT_in),
    .LOAD (LOAD_in),
    .LOAD_EXT (LOAD_EXT_in),
    .OFD_CE (OFD_CE_in),
    .RST (RST_in),
    .RST_DLY (RST_DLY_in),
    .RST_DLY_EXT (RST_DLY_EXT_in),
    .RX_BIT_CTRL_IN (RX_BIT_CTRL_IN_in),
    .RX_DATAIN1 (RX_DATAIN1_in),
    .T (T_in),
    .TX_BIT_CTRL_IN (TX_BIT_CTRL_IN_in),
    .TX_D (TX_D_in),
    .TX_RST (TX_RST_in),
    .SIM_IDELAY_DATAIN0(IDELAY_DATAIN0_out),
    .SIM_IDELAY_DATAOUT(IDELAY_DATAOUT_out),
    .GSR (glblGSR)
  );
end 
endgenerate

`ifdef XIL_TIMING
  wire clk_en_n;
  wire clk_en_p;
  wire clk_ext_en_n;
  wire clk_ext_en_p;
  
  assign clk_en_n =  IS_CLK_INVERTED_BIN;
  assign clk_en_p = ~IS_CLK_INVERTED_BIN;
  assign clk_ext_en_n =  IS_CLK_EXT_INVERTED_BIN;
  assign clk_ext_en_p = ~IS_CLK_EXT_INVERTED_BIN;
`endif

  specify
    (CLK *> CNTVALUEOUT) = (100:100:100, 100:100:100);
    (CLK_EXT *> CNTVALUEOUT_EXT) = (100:100:100, 100:100:100);
    (DATAIN *> Q) = (0:0:0, 0:0:0);
    (DATAIN *> RX_BIT_CTRL_OUT) = (0:0:0, 0:0:0);
    (FIFO_RD_CLK *> Q) = (100:100:100, 100:100:100);
    (FIFO_RD_CLK => FIFO_EMPTY) = (100:100:100, 100:100:100);
    (RX_BIT_CTRL_IN *> FIFO_WRCLK_OUT) = (0:0:0, 0:0:0);
    // (FIFO_WRCLK_OUT => FIFO_EMPTY) = (0:0:0, 0:0:0); // error prop output to output
`ifdef XIL_TIMING
    $period (negedge CLK, 0:0:0, notifier);
    $period (negedge CLK_EXT, 0:0:0, notifier);
    $period (negedge FIFO_RD_CLK, 0:0:0, notifier);
    $period (negedge RX_BIT_CTRL_IN[20], 0:0:0, notifier);
    $period (posedge CLK, 0:0:0, notifier);
    $period (posedge CLK_EXT, 0:0:0, notifier);
    $period (posedge FIFO_RD_CLK, 0:0:0, notifier);
    $period (posedge RX_BIT_CTRL_IN[20], 0:0:0, notifier);
    $setuphold (negedge CLK, negedge CE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CE_delay);
    $setuphold (negedge CLK, negedge CNTVALUEIN, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay);
    $setuphold (negedge CLK, negedge INC, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, INC_delay);
    $setuphold (negedge CLK, negedge LOAD, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, LOAD_delay);
    $setuphold (negedge CLK, posedge CE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CE_delay);
    $setuphold (negedge CLK, posedge CNTVALUEIN, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay);
    $setuphold (negedge CLK, posedge INC, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, INC_delay);
    $setuphold (negedge CLK, posedge LOAD, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, LOAD_delay);
    $setuphold (negedge CLK_EXT, negedge CE_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_n, clk_ext_en_n, CLK_EXT_delay, CE_EXT_delay);
    $setuphold (negedge CLK_EXT, negedge CNTVALUEIN_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_n, clk_ext_en_n, CLK_EXT_delay, CNTVALUEIN_EXT_delay);
    $setuphold (negedge CLK_EXT, negedge INC_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_n, clk_ext_en_n, CLK_EXT_delay, INC_EXT_delay);
    $setuphold (negedge CLK_EXT, negedge LOAD_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_n, clk_ext_en_n, CLK_EXT_delay, LOAD_EXT_delay);
    $setuphold (negedge CLK_EXT, posedge CE_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_n, clk_ext_en_n, CLK_EXT_delay, CE_EXT_delay);
    $setuphold (negedge CLK_EXT, posedge CNTVALUEIN_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_n, clk_ext_en_n, CLK_EXT_delay, CNTVALUEIN_EXT_delay);
    $setuphold (negedge CLK_EXT, posedge INC_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_n, clk_ext_en_n, CLK_EXT_delay, INC_EXT_delay);
    $setuphold (negedge CLK_EXT, posedge LOAD_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_n, clk_ext_en_n, CLK_EXT_delay, LOAD_EXT_delay);
    $setuphold (posedge CLK, negedge CE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CE_delay);
    $setuphold (posedge CLK, negedge CNTVALUEIN, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay);
    $setuphold (posedge CLK, negedge INC, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, INC_delay);
    $setuphold (posedge CLK, negedge LOAD, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, LOAD_delay);
    $setuphold (posedge CLK, posedge CE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CE_delay);
    $setuphold (posedge CLK, posedge CNTVALUEIN, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay);
    $setuphold (posedge CLK, posedge INC, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, INC_delay);
    $setuphold (posedge CLK, posedge LOAD, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, LOAD_delay);
    $setuphold (posedge CLK_EXT, negedge CE_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_p, clk_ext_en_p, CLK_EXT_delay, CE_EXT_delay);
    $setuphold (posedge CLK_EXT, negedge CNTVALUEIN_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_p, clk_ext_en_p, CLK_EXT_delay, CNTVALUEIN_EXT_delay);
    $setuphold (posedge CLK_EXT, negedge INC_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_p, clk_ext_en_p, CLK_EXT_delay, INC_EXT_delay);
    $setuphold (posedge CLK_EXT, negedge LOAD_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_p, clk_ext_en_p, CLK_EXT_delay, LOAD_EXT_delay);
    $setuphold (posedge CLK_EXT, posedge CE_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_p, clk_ext_en_p, CLK_EXT_delay, CE_EXT_delay);
    $setuphold (posedge CLK_EXT, posedge CNTVALUEIN_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_p, clk_ext_en_p, CLK_EXT_delay, CNTVALUEIN_EXT_delay);
    $setuphold (posedge CLK_EXT, posedge INC_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_p, clk_ext_en_p, CLK_EXT_delay, INC_EXT_delay);
    $setuphold (posedge CLK_EXT, posedge LOAD_EXT, 0:0:0, 0:0:0, notifier, clk_ext_en_p, clk_ext_en_p, CLK_EXT_delay, LOAD_EXT_delay);
    $setuphold (posedge FIFO_RD_CLK, negedge FIFO_RD_EN, 0:0:0, 0:0:0, notifier, , , FIFO_RD_CLK_delay, FIFO_RD_EN_delay);
    $setuphold (posedge FIFO_RD_CLK, posedge FIFO_RD_EN, 0:0:0, 0:0:0, notifier, , , FIFO_RD_CLK_delay, FIFO_RD_EN_delay);
    $width (negedge CLK, 0:0:0, 0, notifier);
    $width (negedge CLK_EXT, 0:0:0, 0, notifier);
    $width (negedge FIFO_RD_CLK, 0:0:0, 0, notifier);
    $width (negedge RX_BIT_CTRL_IN[20], 0:0:0, 0, notifier);
    $width (posedge CLK, 0:0:0, 0, notifier);
    $width (posedge CLK_EXT, 0:0:0, 0, notifier);
    $width (posedge FIFO_RD_CLK, 0:0:0, 0, notifier);
    $width (posedge RX_BIT_CTRL_IN[20], 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
