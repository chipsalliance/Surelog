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
//  /   /                        RXTX_BITSLICE
// /___/   /\      Filename    : RXTX_BITSLICE.v
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

module RXTX_BITSLICE #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter ENABLE_PRE_EMPHASIS = "FALSE",
  parameter FIFO_SYNC_MODE = "FALSE",
  parameter [0:0] INIT = 1'b1,
  parameter [0:0] IS_RX_CLK_INVERTED = 1'b0,
  parameter [0:0] IS_RX_RST_DLY_INVERTED = 1'b0,
  parameter [0:0] IS_RX_RST_INVERTED = 1'b0,
  parameter [0:0] IS_TX_CLK_INVERTED = 1'b0,
  parameter [0:0] IS_TX_RST_DLY_INVERTED = 1'b0,
  parameter [0:0] IS_TX_RST_INVERTED = 1'b0,
  parameter LOOPBACK = "FALSE",
  parameter NATIVE_ODELAY_BYPASS = "FALSE",
  parameter RX_DATA_TYPE = "DATA",
  parameter integer RX_DATA_WIDTH = 8,
  parameter RX_DELAY_FORMAT = "TIME",
  parameter RX_DELAY_TYPE = "FIXED",
  parameter integer RX_DELAY_VALUE = 0,
  parameter real RX_REFCLK_FREQUENCY = 300.0,
  parameter RX_UPDATE_MODE = "ASYNC",
  parameter SIM_DEVICE = "ULTRASCALE",
  parameter real SIM_VERSION = 2.0,
  parameter TBYTE_CTL = "TBYTE_IN",
  parameter integer TX_DATA_WIDTH = 8,
  parameter TX_DELAY_FORMAT = "TIME",
  parameter TX_DELAY_TYPE = "FIXED",
  parameter integer TX_DELAY_VALUE = 0,
  parameter TX_OUTPUT_PHASE_90 = "FALSE",
  parameter real TX_REFCLK_FREQUENCY = 300.0,
  parameter TX_UPDATE_MODE = "ASYNC"
)(
  output FIFO_EMPTY,
  output FIFO_WRCLK_OUT,
  output O,
  output [7:0] Q,
  output [39:0] RX_BIT_CTRL_OUT,
  output [8:0] RX_CNTVALUEOUT,
  output [39:0] TX_BIT_CTRL_OUT,
  output [8:0] TX_CNTVALUEOUT,
  output T_OUT,

  input [7:0] D,
  input DATAIN,
  input FIFO_RD_CLK,
  input FIFO_RD_EN,
  input [39:0] RX_BIT_CTRL_IN,
  input RX_CE,
  input RX_CLK,
  input [8:0] RX_CNTVALUEIN,
  input RX_EN_VTC,
  input RX_INC,
  input RX_LOAD,
  input RX_RST,
  input RX_RST_DLY,
  input T,
  input TBYTE_IN,
  input [39:0] TX_BIT_CTRL_IN,
  input TX_CE,
  input TX_CLK,
  input [8:0] TX_CNTVALUEIN,
  input TX_EN_VTC,
  input TX_INC,
  input TX_LOAD,
  input TX_RST,
  input TX_RST_DLY
);

// define constants
  localparam MODULE_NAME = "RXTX_BITSLICE";
  localparam in_delay    = 0;
  localparam out_delay   = 0;
  localparam inclk_delay    = 0;
  localparam outclk_delay   = 0;

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only

  reg warning_flag = 1'b1;
`ifdef XIL_DR
  `include "RXTX_BITSLICE_dr.v"
`else
  localparam [40:1] ENABLE_PRE_EMPHASIS_REG = ENABLE_PRE_EMPHASIS;
  localparam [40:1] FIFO_SYNC_MODE_REG = FIFO_SYNC_MODE;
  localparam [0:0] INIT_REG = INIT;
  localparam [0:0] IS_RX_CLK_INVERTED_REG = IS_RX_CLK_INVERTED;
  localparam [0:0] IS_RX_RST_DLY_INVERTED_REG = IS_RX_RST_DLY_INVERTED;
  localparam [0:0] IS_RX_RST_INVERTED_REG = IS_RX_RST_INVERTED;
  localparam [0:0] IS_TX_CLK_INVERTED_REG = IS_TX_CLK_INVERTED;
  localparam [0:0] IS_TX_RST_DLY_INVERTED_REG = IS_TX_RST_DLY_INVERTED;
  localparam [0:0] IS_TX_RST_INVERTED_REG = IS_TX_RST_INVERTED;
  localparam [40:1] LOOPBACK_REG = LOOPBACK;
  localparam [40:1] NATIVE_ODELAY_BYPASS_REG = NATIVE_ODELAY_BYPASS;
  localparam [112:1] RX_DATA_TYPE_REG = RX_DATA_TYPE;
  localparam [31:0] RX_DATA_WIDTH_REG = RX_DATA_WIDTH;
  localparam [40:1] RX_DELAY_FORMAT_REG = RX_DELAY_FORMAT;
  localparam [64:1] RX_DELAY_TYPE_REG = RX_DELAY_TYPE;
  localparam [31:0] RX_DELAY_VALUE_REG = RX_DELAY_VALUE;
  localparam real RX_REFCLK_FREQUENCY_REG = RX_REFCLK_FREQUENCY;
  localparam [48:1] RX_UPDATE_MODE_REG = RX_UPDATE_MODE;
  localparam [152:1] SIM_DEVICE_REG = SIM_DEVICE;
  localparam real SIM_VERSION_REG = SIM_VERSION;
  localparam [64:1] TBYTE_CTL_REG = TBYTE_CTL;
  localparam [31:0] TX_DATA_WIDTH_REG = TX_DATA_WIDTH;
  localparam [40:1] TX_DELAY_FORMAT_REG = TX_DELAY_FORMAT;
  localparam [64:1] TX_DELAY_TYPE_REG = TX_DELAY_TYPE;
  localparam [31:0] TX_DELAY_VALUE_REG = TX_DELAY_VALUE;
  localparam [40:1] TX_OUTPUT_PHASE_90_REG = TX_OUTPUT_PHASE_90;
  localparam real TX_REFCLK_FREQUENCY_REG = TX_REFCLK_FREQUENCY;
  localparam [48:1] TX_UPDATE_MODE_REG = TX_UPDATE_MODE;
`endif

  localparam [40:1] DDR_DIS_DQS_REG = "TRUE";
  localparam [40:1] FIFO_ENABLE_REG = "TRUE";
  localparam [5:0] SPARE_REG = 6'b000000;
  localparam [0:0] RX_DC_ADJ_EN_REG = 1'b0;
  localparam [2:0] RX_FDLY_REG = 3'b010;
  localparam [40:1] RX_Q4_ROUTETHRU_REG = "FALSE";
  localparam [40:1] RX_Q5_ROUTETHRU_REG = "FALSE";
  localparam [40:1] TXRX_LOOPBACK_REG = "FALSE";
  localparam [0:0] TX_DC_ADJ_EN_REG = 1'b0;
  localparam [2:0] TX_FDLY_REG = 3'b010;
  localparam [40:1] TX_Q_ROUTETHRU_REG = "FALSE";
  localparam [40:1] TX_T_OUT_ROUTETHRU_REG = "FALSE";
  localparam [40:1] XIPHY_BITSLICE_MODE_REG = "TRUE";

  wire IS_RX_CLK_INVERTED_BIN;
  wire IS_RX_RST_DLY_INVERTED_BIN;
  wire IS_RX_RST_INVERTED_BIN;
  wire IS_TX_CLK_INVERTED_BIN;
  wire IS_TX_RST_DLY_INVERTED_BIN;
  wire IS_TX_RST_INVERTED_BIN;
  wire [63:0] RX_REFCLK_FREQUENCY_BIN;
  wire [63:0] SIM_VERSION_BIN;
  wire [63:0] TX_REFCLK_FREQUENCY_BIN;

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif
  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR;

  wire IDELAY_DATAIN0_out;
  wire IDELAY_DATAOUT_out;
  wire ODELAY_DATAIN0_out;
  wire ODELAY_DATAOUT_out;

  wire FIFO_EMPTY_out;
  wire FIFO_WRCLK_OUT_out;
  wire O_out;
  wire TX2RX_CASC_OUT_out;
  wire T_OUT_out;
  wire [39:0] RX_BIT_CTRL_OUT_out;
  wire [39:0] TX_BIT_CTRL_OUT_out;
  wire [7:0] Q_out;
  wire [8:0] RX_CNTVALUEOUT_out;
  wire [8:0] TX_CNTVALUEOUT_out;

  wire FIFO_EMPTY_delay;
  wire FIFO_WRCLK_OUT_delay;
  wire O_delay;
  wire T_OUT_delay;
  wire [39:0] RX_BIT_CTRL_OUT_delay;
  wire [39:0] TX_BIT_CTRL_OUT_delay;
  wire [7:0] Q_delay;
  wire [8:0] RX_CNTVALUEOUT_delay;
  wire [8:0] TX_CNTVALUEOUT_delay;

  wire DATAIN_in;
  wire FIFO_RD_CLK_in;
  wire FIFO_RD_EN_in;
  wire IFD_CE_in;
  wire OFD_CE_in;
  wire RX2TX_CASC_RETURN_IN_in;
  wire RX_CE_in;
  wire RX_CLKDIV_in;
  wire RX_CLK_C_B_in;
  wire RX_CLK_C_in;
  wire RX_CLK_in;
  wire RX_DATAIN1_in;
  wire RX_EN_VTC_in;
  wire RX_INC_in;
  wire RX_LOAD_in;
  wire RX_RST_DLY_in;
  wire RX_RST_in;
  wire TBYTE_IN_in;
  wire TX2RX_CASC_IN_in;
  wire TX_CE_in;
  wire TX_CLK_in;
  wire TX_EN_VTC_in;
  wire TX_INC_in;
  wire TX_LOAD_in;
  wire TX_OCLKDIV_in;
  wire TX_OCLK_in;
  wire TX_RST_DLY_in;
  wire TX_RST_in;
  wire T_in;
  wire [39:0] RX_BIT_CTRL_IN_in;
  wire [39:0] TX_BIT_CTRL_IN_in;
  wire [7:0] D_in;
  wire [8:0] RX_CNTVALUEIN_in;
  wire [8:0] TX_CNTVALUEIN_in;

  wire DATAIN_delay;
  wire FIFO_RD_CLK_delay;
  wire FIFO_RD_EN_delay;
  wire RX_CE_delay;
  wire RX_CLK_delay;
  wire RX_EN_VTC_delay;
  wire RX_INC_delay;
  wire RX_LOAD_delay;
  wire RX_RST_DLY_delay;
  wire RX_RST_delay;
  wire TBYTE_IN_delay;
  wire TX_CE_delay;
  wire TX_CLK_delay;
  wire TX_EN_VTC_delay;
  wire TX_INC_delay;
  wire TX_LOAD_delay;
  wire TX_RST_DLY_delay;
  wire TX_RST_delay;
  wire T_delay;
  wire [39:0] RX_BIT_CTRL_IN_delay;
  wire [39:0] TX_BIT_CTRL_IN_delay;
  wire [7:0] D_delay;
  wire [8:0] RX_CNTVALUEIN_delay;
  wire [8:0] TX_CNTVALUEIN_delay;

  assign #(out_delay) FIFO_EMPTY = FIFO_EMPTY_delay;
  assign #(out_delay) FIFO_WRCLK_OUT = FIFO_WRCLK_OUT_delay;
  assign #(out_delay) O = O_delay;
  assign #(out_delay) Q = Q_delay;
  assign #(out_delay) RX_BIT_CTRL_OUT = RX_BIT_CTRL_OUT_delay;
  assign #(out_delay) RX_CNTVALUEOUT = (RX_EN_VTC_in ===  1'b1) ? 9'bxxxxxxxxx : RX_CNTVALUEOUT_delay;
  assign #(out_delay) TX_BIT_CTRL_OUT = TX_BIT_CTRL_OUT_delay;
  assign #(out_delay) TX_CNTVALUEOUT = (TX_EN_VTC_in ===  1'b1) ? 9'bxxxxxxxxx : TX_CNTVALUEOUT_delay;
  assign #(out_delay) T_OUT = T_OUT_delay;

`ifdef XIL_TIMING
  reg notifier;
`endif

`ifndef XIL_TIMING // inputs with timing checks
  assign #(inclk_delay) FIFO_RD_CLK_delay = FIFO_RD_CLK;
  assign #(inclk_delay) RX_CLK_delay = RX_CLK;
  assign #(inclk_delay) TX_CLK_delay = TX_CLK;

  assign #(in_delay) D_delay = D;
  assign #(in_delay) FIFO_RD_EN_delay = FIFO_RD_EN;
  assign #(in_delay) RX_CE_delay = RX_CE;
  assign #(in_delay) RX_CNTVALUEIN_delay = RX_CNTVALUEIN;
  assign #(in_delay) RX_INC_delay = RX_INC;
  assign #(in_delay) RX_LOAD_delay = RX_LOAD;
  assign #(in_delay) TX_CE_delay = TX_CE;
  assign #(in_delay) TX_CNTVALUEIN_delay = TX_CNTVALUEIN;
  assign #(in_delay) TX_INC_delay = TX_INC;
  assign #(in_delay) TX_LOAD_delay = TX_LOAD;
  assign #(in_delay) TX_BIT_CTRL_IN_delay[25] = TX_BIT_CTRL_IN[25];
  assign #(in_delay) TX_BIT_CTRL_IN_delay[26] = TX_BIT_CTRL_IN[26];  
`endif

// inputs with no timing checks
  assign #(in_delay) DATAIN_delay = DATAIN;
  assign #(in_delay) RX_BIT_CTRL_IN_delay = RX_BIT_CTRL_IN;
  assign #(in_delay) RX_EN_VTC_delay = RX_EN_VTC;
  assign #(in_delay) RX_RST_DLY_delay = RX_RST_DLY;
  assign #(in_delay) RX_RST_delay = RX_RST;
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
  assign #(in_delay) TX_EN_VTC_delay = TX_EN_VTC;
  assign #(in_delay) TX_RST_DLY_delay = TX_RST_DLY;
  assign #(in_delay) TX_RST_delay = TX_RST;
  assign #(in_delay) T_delay = T;

  assign FIFO_EMPTY_delay = FIFO_EMPTY_out;
  assign FIFO_WRCLK_OUT_delay = FIFO_WRCLK_OUT_out;
  assign O_delay = O_out;
  assign Q_delay = Q_out;
  assign RX_BIT_CTRL_OUT_delay = RX_BIT_CTRL_OUT_out;
  assign RX_CNTVALUEOUT_delay = RX_CNTVALUEOUT_out;
  assign TX_BIT_CTRL_OUT_delay = TX_BIT_CTRL_OUT_out;
  assign TX_CNTVALUEOUT_delay = TX_CNTVALUEOUT_out;
  assign T_OUT_delay = T_OUT_out;

  assign DATAIN_in = DATAIN_delay;
  assign D_in = D_delay;
  assign FIFO_RD_CLK_in = FIFO_RD_CLK_delay;
  assign FIFO_RD_EN_in = FIFO_RD_EN_delay;
  assign RX_BIT_CTRL_IN_in = RX_BIT_CTRL_IN_delay;
  assign RX_CE_in = RX_CE_delay;
  assign RX_CLK_in = RX_CLK_delay ^ IS_RX_CLK_INVERTED_BIN;
  assign RX_CNTVALUEIN_in = RX_CNTVALUEIN_delay;
  assign RX_EN_VTC_in = RX_EN_VTC_delay;
  assign RX_INC_in = RX_INC_delay;
  assign RX_LOAD_in = RX_LOAD_delay;
  assign RX_RST_DLY_in = RX_RST_DLY_delay ^ IS_RX_RST_DLY_INVERTED_BIN;
  assign RX_RST_in = RX_RST_delay ^ IS_RX_RST_INVERTED_BIN;
  assign TBYTE_IN_in = TBYTE_IN_delay;
  assign TX_BIT_CTRL_IN_in = TX_BIT_CTRL_IN_delay;
  assign TX_CE_in = TX_CE_delay;
  assign TX_CLK_in = TX_CLK_delay ^ IS_TX_CLK_INVERTED_BIN;
  assign TX_CNTVALUEIN_in = TX_CNTVALUEIN_delay;
  assign TX_EN_VTC_in = TX_EN_VTC_delay;
  assign TX_INC_in = TX_INC_delay;
  assign TX_LOAD_in = TX_LOAD_delay;
  assign TX_RST_DLY_in = TX_RST_DLY_delay ^ IS_TX_RST_DLY_INVERTED_BIN;
  assign TX_RST_in = TX_RST_delay ^ IS_TX_RST_INVERTED_BIN;
  assign T_in = T_delay;

  assign IS_RX_CLK_INVERTED_BIN = IS_RX_CLK_INVERTED_REG;
  
  assign IS_RX_RST_DLY_INVERTED_BIN = IS_RX_RST_DLY_INVERTED_REG;
  
  assign IS_RX_RST_INVERTED_BIN = IS_RX_RST_INVERTED_REG;
  
  assign IS_TX_CLK_INVERTED_BIN = IS_TX_CLK_INVERTED_REG;
  
  assign IS_TX_RST_DLY_INVERTED_BIN = IS_TX_RST_DLY_INVERTED_REG;
  
  assign IS_TX_RST_INVERTED_BIN = IS_TX_RST_INVERTED_REG;
  
  assign RX_REFCLK_FREQUENCY_BIN = RX_REFCLK_FREQUENCY_REG * 1000;
  
  assign SIM_VERSION_BIN = SIM_VERSION_REG * 1000;
  
  assign TX_REFCLK_FREQUENCY_BIN = TX_REFCLK_FREQUENCY_REG * 1000;
  
  initial begin
    #1;
    trig_attr = ~trig_attr;
  end

   always @(RX_EN_VTC_in or TX_EN_VTC_in) begin
   if ((RX_EN_VTC_in ===0 || TX_EN_VTC_in ===0 )&& (RX_DELAY_FORMAT_REG == "TIME" || TX_DELAY_FORMAT_REG == "TIME") && warning_flag == 1'b1 ) begin
  $display("Warning: [Unisim %s-1] BISC Calibration : DELAY_FORMAT set to TIME with RX_EN_VTC/TX_EN_VTC signal set to 0. In hardware, when the RX_EN_VTC/TX_EN_VTC signal is low during the initial calibration process, the BISC will never complete and the DLY_RDY and VTC_RDY status signals from the BITSLICE_CONTROL remain low. Simulation will not reflect this behavior. In simulation, the DLY_RDY and VTC_RDY from the BITSLICE_CONTROL will assert high. You should ensure the RX_EN_VTC/TX_EN_VTC signal is held high during initial BISC self calibration to ensure BISC completes in hardware. See Select IO Userguide UG571 for more information.Instance: %m", MODULE_NAME);
     warning_flag = 1'b0;
   end
   end


  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((ENABLE_PRE_EMPHASIS_REG != "FALSE") &&
         (ENABLE_PRE_EMPHASIS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-102] ENABLE_PRE_EMPHASIS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, ENABLE_PRE_EMPHASIS_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((FIFO_SYNC_MODE_REG != "FALSE") &&
         (FIFO_SYNC_MODE_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-103] FIFO_SYNC_MODE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, FIFO_SYNC_MODE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((LOOPBACK_REG != "FALSE") &&
         (LOOPBACK_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-111] LOOPBACK attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, LOOPBACK_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((NATIVE_ODELAY_BYPASS_REG != "FALSE") &&
         (NATIVE_ODELAY_BYPASS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-112] NATIVE_ODELAY_BYPASS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, NATIVE_ODELAY_BYPASS_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((RX_DATA_TYPE_REG != "DATA") &&
         (RX_DATA_TYPE_REG != "CLOCK") &&
         (RX_DATA_TYPE_REG != "DATA_AND_CLOCK") &&
         (RX_DATA_TYPE_REG != "SERIAL"))) begin
      $display("Error: [Unisim %s-113] RX_DATA_TYPE attribute is set to %s.  Legal values for this attribute are DATA, CLOCK, DATA_AND_CLOCK or SERIAL. Instance: %m", MODULE_NAME, RX_DATA_TYPE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((RX_DATA_WIDTH_REG != 8) &&
         (RX_DATA_WIDTH_REG != 4))) begin
      $display("Error: [Unisim %s-114] RX_DATA_WIDTH attribute is set to %d.  Legal values for this attribute are 8 or 4. Instance: %m", MODULE_NAME, RX_DATA_WIDTH_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((RX_DELAY_FORMAT_REG != "TIME") &&
         (RX_DELAY_FORMAT_REG != "COUNT"))) begin
      $display("Error: [Unisim %s-116] RX_DELAY_FORMAT attribute is set to %s.  Legal values for this attribute are TIME or COUNT. Instance: %m", MODULE_NAME, RX_DELAY_FORMAT_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((RX_DELAY_TYPE_REG != "FIXED") &&
         (RX_DELAY_TYPE_REG != "VAR_LOAD") &&
         (RX_DELAY_TYPE_REG != "VARIABLE"))) begin
      $display("Error: [Unisim %s-117] RX_DELAY_TYPE attribute is set to %s.  Legal values for this attribute are FIXED, VAR_LOAD or VARIABLE. Instance: %m", MODULE_NAME, RX_DELAY_TYPE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        (SIM_DEVICE_REG == "ULTRASCALE" && ((RX_DELAY_VALUE_REG < 0) || (RX_DELAY_VALUE_REG > 1250)))) begin
      $display("Error: [Unisim %s-118] RX_DELAY_VALUE attribute is set to %d.  Legal values for this attribute are 0 to 1250. Instance: %m", MODULE_NAME, RX_DELAY_VALUE_REG);
      attr_err = 1'b1;
    end
    if ((attr_test == 1'b1) ||
        (SIM_DEVICE_REG != "ULTRASCALE" && ((RX_DELAY_VALUE_REG < 0) || (RX_DELAY_VALUE_REG > 1100)))) begin
      $display("Error: [Unisim %s-118] RX_DELAY_VALUE attribute is set to %d.  Legal values for this attribute are 0 to 1100. Instance: %m", MODULE_NAME, RX_DELAY_VALUE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        (RX_DELAY_FORMAT_REG != "COUNT" && SIM_DEVICE_REG != "ULTRASCALE" && (RX_REFCLK_FREQUENCY_REG < 300.0 || RX_REFCLK_FREQUENCY_REG > 2667.0))) begin
      $display("Error: [Unisim %s-122] RX_REFCLK_FREQUENCY attribute is set to %f.  Legal values for this attribute are 300.0 to 2667.0. Instance: %m", MODULE_NAME, RX_REFCLK_FREQUENCY_REG);
      attr_err = 1'b1;
    end
    if ((attr_test == 1'b1) ||
        (RX_DELAY_FORMAT_REG != "COUNT" && SIM_DEVICE_REG == "ULTRASCALE" && (RX_REFCLK_FREQUENCY_REG < 200.0 || RX_REFCLK_FREQUENCY_REG > 2400.0))) begin
      $display("Error: [Unisim %s-122] RX_REFCLK_FREQUENCY attribute is set to %f.  Legal values for this attribute are 200.0 to 2400.0. Instance: %m", MODULE_NAME, RX_REFCLK_FREQUENCY_REG);
      attr_err = 1'b1;
    end    
    if ((attr_test == 1'b1) ||
        ((RX_UPDATE_MODE_REG != "ASYNC") &&
         (RX_UPDATE_MODE_REG != "MANUAL") &&
         (RX_UPDATE_MODE_REG != "SYNC"))) begin
      $display("Error: [Unisim %s-123] RX_UPDATE_MODE attribute is set to %s.  Legal values for this attribute are ASYNC, MANUAL or SYNC. Instance: %m", MODULE_NAME, RX_UPDATE_MODE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2"))) begin
      $display("Error: [Unisim %s-124] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE, ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1 or ULTRASCALE_PLUS_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
       ((SIM_VERSION_REG != 2.0) &&
        (SIM_VERSION_REG != 1.0))) begin
      $display("Error: [Unisim %s-125] SIM_VERSION attribute is set to %f.  Legal values for this attribute are 2.0 or 1.0. Instance: %m", MODULE_NAME, SIM_VERSION_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((TBYTE_CTL_REG != "TBYTE_IN") &&
         (TBYTE_CTL_REG != "T"))) begin
      $display("Error: [Unisim %s-126] TBYTE_CTL attribute is set to %s.  Legal values for this attribute are TBYTE_IN or T. Instance: %m", MODULE_NAME, TBYTE_CTL_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((TX_DATA_WIDTH_REG != 8) &&
         (TX_DATA_WIDTH_REG != 4))) begin
      $display("Error: [Unisim %s-128] TX_DATA_WIDTH attribute is set to %d.  Legal values for this attribute are 8 or 4. Instance: %m", MODULE_NAME, TX_DATA_WIDTH_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((TX_DELAY_FORMAT_REG != "TIME") &&
         (TX_DELAY_FORMAT_REG != "COUNT"))) begin
      $display("Error: [Unisim %s-130] TX_DELAY_FORMAT attribute is set to %s.  Legal values for this attribute are TIME or COUNT. Instance: %m", MODULE_NAME, TX_DELAY_FORMAT_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((TX_DELAY_TYPE_REG != "FIXED") &&
         (TX_DELAY_TYPE_REG != "VAR_LOAD") &&
         (TX_DELAY_TYPE_REG != "VARIABLE"))) begin
      $display("Error: [Unisim %s-131] TX_DELAY_TYPE attribute is set to %s.  Legal values for this attribute are FIXED, VAR_LOAD or VARIABLE. Instance: %m", MODULE_NAME, TX_DELAY_TYPE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        (SIM_DEVICE_REG == "ULTRASCALE" && ((TX_DELAY_VALUE_REG < 0) || (TX_DELAY_VALUE_REG > 1250)))) begin
      $display("Error: [Unisim %s-132] TX_DELAY_VALUE attribute is set to %d.  Legal values for this attribute are 0 to 1250. Instance: %m", MODULE_NAME, TX_DELAY_VALUE_REG);
      attr_err = 1'b1;
    end
    if ((attr_test == 1'b1) ||
        (SIM_DEVICE_REG != "ULTRASCALE" && ((TX_DELAY_VALUE_REG < 0) || (TX_DELAY_VALUE_REG > 1100)))) begin
      $display("Error: [Unisim %s-132] TX_DELAY_VALUE attribute is set to %d.  Legal values for this attribute are 0 to 1100. Instance: %m", MODULE_NAME, TX_DELAY_VALUE_REG);
      attr_err = 1'b1;
    end
  
    if ((attr_test == 1'b1) ||
        ((TX_OUTPUT_PHASE_90_REG != "FALSE") &&
         (TX_OUTPUT_PHASE_90_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-134] TX_OUTPUT_PHASE_90 attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, TX_OUTPUT_PHASE_90_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        (TX_DELAY_FORMAT_REG != "COUNT" && SIM_DEVICE_REG != "ULTRASCALE" && (TX_REFCLK_FREQUENCY_REG < 300.0 || TX_REFCLK_FREQUENCY_REG > 2667.0))) begin
      $display("Error: [Unisim %s-136] TX_REFCLK_FREQUENCY attribute is set to %f.  Legal values for this attribute are 300.0 to 2667.0. Instance: %m", MODULE_NAME, TX_REFCLK_FREQUENCY_REG);
      attr_err = 1'b1;
    end
    if ((attr_test == 1'b1) ||
        (TX_DELAY_FORMAT_REG != "COUNT" && SIM_DEVICE_REG == "ULTRASCALE" && (TX_REFCLK_FREQUENCY_REG < 200.0 || TX_REFCLK_FREQUENCY_REG > 2400.0))) begin
      $display("Error: [Unisim %s-136] TX_REFCLK_FREQUENCY attribute is set to %f.  Legal values for this attribute are 200.0 to 2400.0. Instance: %m", MODULE_NAME, TX_REFCLK_FREQUENCY_REG);
      attr_err = 1'b1;
    end    
    if ((attr_test == 1'b1) ||
        ((TX_UPDATE_MODE_REG != "ASYNC") &&
         (TX_UPDATE_MODE_REG != "MANUAL") &&
         (TX_UPDATE_MODE_REG != "SYNC"))) begin
      $display("Error: [Unisim %s-138] TX_UPDATE_MODE attribute is set to %s.  Legal values for this attribute are ASYNC, MANUAL or SYNC. Instance: %m", MODULE_NAME, TX_UPDATE_MODE_REG);
      attr_err = 1'b1;
    end
   
    if ((attr_test == 1'b1) ||
        (TX_DELAY_FORMAT_REG != RX_DELAY_FORMAT_REG)) begin
      $display("Error: [Unisim %s-139] TX_DELAY_FORMAT = %s is not same as RX_DELAY_FORMAT = %s. [RX/TX]_DELAY_FORMAT attributes must be set to same value. Instance: %m", MODULE_NAME, TX_DELAY_FORMAT_REG, RX_DELAY_FORMAT_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (RX_DELAY_FORMAT_REG == TX_DELAY_FORMAT_REG && TX_DELAY_FORMAT_REG == "TIME" && TX_DELAY_VALUE_REG != RX_DELAY_VALUE_REG)) begin
      $display("Error: [Unisim %s-140] [RX/TX]_DELAY_FORMAT is set to TIME and TX_DELAY_VALUE is set to %d is and RX_DELAY_VALUE is set to %d. Both RX_DELAY_VALUE and TX_DELAY_VALUE must be set to same value when [RX/TX]_DELAY_FORMAT is set to TIME. Instance: %m", MODULE_NAME, TX_DELAY_VALUE_REG, RX_DELAY_VALUE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (TX_REFCLK_FREQUENCY_REG != RX_REFCLK_FREQUENCY_REG)) begin
      $display("Error: [Unisim %s-141] TX_REFCLK_FREQUENCY = %f is not same as RX_REFCLK_FREQUENCY = %f. [RX/TX]_REFCLK_FREQUENCY attributes must be set to same value. Instance: %m", MODULE_NAME, TX_REFCLK_FREQUENCY_REG, RX_REFCLK_FREQUENCY_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (TX_DATA_WIDTH_REG != RX_DATA_WIDTH_REG)) begin
      $display("Error: [Unisim %s-142] TX_DATA_WIDTH is set to %d and RX_DATA_WIDTH is set to %d. Both RX_DATA_WIDTH and TX_DATA_WIDTH attributes must be set to same value. Instance: %m", MODULE_NAME, TX_DATA_WIDTH_REG, RX_DATA_WIDTH_REG);
      attr_err = 1'b1;
    end


    if (attr_err == 1'b1) #1 $finish;
  end

  assign RX_CLKDIV_in = 1'b1; // tie off
  assign RX_CLK_C_B_in = 1'b1; // tie off
  assign RX_CLK_C_in = 1'b1; // tie off
  assign TX_OCLKDIV_in = 1'b1; // tie off
  assign TX_OCLK_in = 1'b1; // tie off

  assign IFD_CE_in = 1'b0; // tie off
  assign OFD_CE_in = 1'b0; // tie off
  assign RX2TX_CASC_RETURN_IN_in = 1'b1; // tie off
  assign RX_DATAIN1_in = 1'b0; // tie off
  assign TX2RX_CASC_IN_in = 1'b1; // tie off

generate

if ((SIM_DEVICE == "ULTRASCALE_PLUS") || (SIM_DEVICE == "ULTRASCALE_PLUS_ES1") || (SIM_DEVICE == "ULTRASCALE_PLUS_ES2")) begin : generate_block1
  SIP_RXTX_BITSLICE_D1 SIP_RXTX_BITSLICE_INST (
    .DDR_DIS_DQS (DDR_DIS_DQS_REG),
    .ENABLE_PRE_EMPHASIS (ENABLE_PRE_EMPHASIS_REG),
    .FIFO_SYNC_MODE (FIFO_SYNC_MODE_REG),
    .FIFO_ENABLE (FIFO_ENABLE_REG),
    .SPARE (SPARE_REG),
    .INIT (INIT_REG),
    .LOOPBACK (LOOPBACK_REG),
    .NATIVE_ODELAY_BYPASS (NATIVE_ODELAY_BYPASS_REG),
    .RX_DATA_TYPE (RX_DATA_TYPE_REG),
    .RX_DATA_WIDTH (RX_DATA_WIDTH_REG),
    .RX_DC_ADJ_EN (RX_DC_ADJ_EN_REG),
    .RX_DELAY_FORMAT (RX_DELAY_FORMAT_REG),
    .RX_DELAY_TYPE (RX_DELAY_TYPE_REG),
    .RX_DELAY_VALUE (RX_DELAY_VALUE_REG),
    .RX_FDLY (RX_FDLY_REG),
    .RX_Q4_ROUTETHRU (RX_Q4_ROUTETHRU_REG),
    .RX_Q5_ROUTETHRU (RX_Q5_ROUTETHRU_REG),
    .RX_REFCLK_FREQUENCY (RX_REFCLK_FREQUENCY_BIN),
    .RX_UPDATE_MODE (RX_UPDATE_MODE_REG),
    .TBYTE_CTL (TBYTE_CTL_REG),
    .TXRX_LOOPBACK (TXRX_LOOPBACK_REG),
    .TX_DATA_WIDTH (TX_DATA_WIDTH_REG),
    .TX_DC_ADJ_EN (TX_DC_ADJ_EN_REG),
    .TX_DELAY_FORMAT (TX_DELAY_FORMAT_REG),
    .TX_DELAY_TYPE (TX_DELAY_TYPE_REG),
    .TX_DELAY_VALUE (TX_DELAY_VALUE_REG),
    .TX_FDLY (TX_FDLY_REG),
    .TX_OUTPUT_PHASE_90 (TX_OUTPUT_PHASE_90_REG),
    .TX_Q_ROUTETHRU (TX_Q_ROUTETHRU_REG),
    .TX_REFCLK_FREQUENCY (TX_REFCLK_FREQUENCY_BIN),
    .TX_T_OUT_ROUTETHRU (TX_T_OUT_ROUTETHRU_REG),
    .TX_UPDATE_MODE (TX_UPDATE_MODE_REG),
    .XIPHY_BITSLICE_MODE (XIPHY_BITSLICE_MODE_REG),
    .FIFO_EMPTY (FIFO_EMPTY_out),
    .FIFO_WRCLK_OUT (FIFO_WRCLK_OUT_out),
    .O (O_out),
    .Q (Q_out),
    .RX_BIT_CTRL_OUT (RX_BIT_CTRL_OUT_out),
    .RX_CNTVALUEOUT (RX_CNTVALUEOUT_out),
    .TX2RX_CASC_OUT (TX2RX_CASC_OUT_out),
    .TX_BIT_CTRL_OUT (TX_BIT_CTRL_OUT_out),
    .TX_CNTVALUEOUT (TX_CNTVALUEOUT_out),
    .T_OUT (T_OUT_out),
    .D (D_in),
    .DATAIN (DATAIN_in),
    .FIFO_RD_CLK (FIFO_RD_CLK_in),
    .FIFO_RD_EN (FIFO_RD_EN_in),
    .IFD_CE (IFD_CE_in),
    .OFD_CE (OFD_CE_in),
    .RX2TX_CASC_RETURN_IN (RX2TX_CASC_RETURN_IN_in),
    .RX_BIT_CTRL_IN (RX_BIT_CTRL_IN_in),
    .RX_CE (RX_CE_in),
    .RX_CLK (RX_CLK_in),
    .RX_CLKDIV (RX_CLKDIV_in),
    .RX_CLK_C (RX_CLK_C_in),
    .RX_CLK_C_B (RX_CLK_C_B_in),
    .RX_CNTVALUEIN (RX_CNTVALUEIN_in),
    .RX_DATAIN1 (RX_DATAIN1_in),
    .RX_EN_VTC (RX_EN_VTC_in),
    .RX_INC (RX_INC_in),
    .RX_LOAD (RX_LOAD_in),
    .RX_RST (RX_RST_in),
    .RX_RST_DLY (RX_RST_DLY_in),
    .T (T_in),
    .TBYTE_IN (TBYTE_IN_in),
    .TX2RX_CASC_IN (TX2RX_CASC_IN_in),
    .TX_BIT_CTRL_IN (TX_BIT_CTRL_IN_in),
    .TX_CE (TX_CE_in),
    .TX_CLK (TX_CLK_in),
    .TX_CNTVALUEIN (TX_CNTVALUEIN_in),
    .TX_EN_VTC (TX_EN_VTC_in),
    .TX_INC (TX_INC_in),
    .TX_LOAD (TX_LOAD_in),
    .TX_OCLK (TX_OCLK_in),
    .TX_OCLKDIV (TX_OCLKDIV_in),
    .TX_RST (TX_RST_in),
    .TX_RST_DLY (TX_RST_DLY_in),
    .SIM_IDELAY_DATAIN0(IDELAY_DATAIN0_out),
    .SIM_IDELAY_DATAOUT(IDELAY_DATAOUT_out),
    .SIM_ODELAY_DATAIN0(ODELAY_DATAIN0_out),
    .SIM_ODELAY_DATAOUT(ODELAY_DATAOUT_out),
    .GSR (glblGSR)
  );
 end else if (SIM_DEVICE == "ULTRASCALE") begin : generate_block1

  SIP_RXTX_BITSLICE_K2 SIP_RXTX_BITSLICE_INST (
    .DDR_DIS_DQS (DDR_DIS_DQS_REG),
    .ENABLE_PRE_EMPHASIS (ENABLE_PRE_EMPHASIS_REG),
    .FIFO_SYNC_MODE (FIFO_SYNC_MODE_REG),
    .INIT (INIT_REG),
    .LOOPBACK (LOOPBACK_REG),
    .NATIVE_ODELAY_BYPASS (NATIVE_ODELAY_BYPASS_REG),
    .RX_DATA_TYPE (RX_DATA_TYPE_REG),
    .RX_DATA_WIDTH (RX_DATA_WIDTH_REG),
    .RX_DC_ADJ_EN (RX_DC_ADJ_EN_REG),
    .RX_DELAY_FORMAT (RX_DELAY_FORMAT_REG),
    .RX_DELAY_TYPE (RX_DELAY_TYPE_REG),
    .RX_DELAY_VALUE (RX_DELAY_VALUE_REG),
    .RX_FDLY (RX_FDLY_REG),
    .RX_Q4_ROUTETHRU (RX_Q4_ROUTETHRU_REG),
    .RX_Q5_ROUTETHRU (RX_Q5_ROUTETHRU_REG),
    .RX_REFCLK_FREQUENCY (RX_REFCLK_FREQUENCY_BIN),
    .RX_UPDATE_MODE (RX_UPDATE_MODE_REG),
    .SIM_VERSION (SIM_VERSION_BIN),
    .TBYTE_CTL (TBYTE_CTL_REG),
    .TXRX_LOOPBACK (TXRX_LOOPBACK_REG),
    .TX_DATA_WIDTH (TX_DATA_WIDTH_REG),
    .TX_DC_ADJ_EN (TX_DC_ADJ_EN_REG),
    .TX_DELAY_FORMAT (TX_DELAY_FORMAT_REG),
    .TX_DELAY_TYPE (TX_DELAY_TYPE_REG),
    .TX_DELAY_VALUE (TX_DELAY_VALUE_REG),
    .TX_FDLY (TX_FDLY_REG),
    .TX_OUTPUT_PHASE_90 (TX_OUTPUT_PHASE_90_REG),
    .TX_Q_ROUTETHRU (TX_Q_ROUTETHRU_REG),
    .TX_REFCLK_FREQUENCY (TX_REFCLK_FREQUENCY_BIN),
    .TX_T_OUT_ROUTETHRU (TX_T_OUT_ROUTETHRU_REG),
    .TX_UPDATE_MODE (TX_UPDATE_MODE_REG),
    .XIPHY_BITSLICE_MODE (XIPHY_BITSLICE_MODE_REG),
    .FIFO_EMPTY (FIFO_EMPTY_out),
    .FIFO_WRCLK_OUT (FIFO_WRCLK_OUT_out),
    .O (O_out),
    .Q (Q_out),
    .RX_BIT_CTRL_OUT (RX_BIT_CTRL_OUT_out),
    .RX_CNTVALUEOUT (RX_CNTVALUEOUT_out),
    .TX2RX_CASC_OUT (TX2RX_CASC_OUT_out),
    .TX_BIT_CTRL_OUT (TX_BIT_CTRL_OUT_out),
    .TX_CNTVALUEOUT (TX_CNTVALUEOUT_out),
    .T_OUT (T_OUT_out),
    .D (D_in),
    .DATAIN (DATAIN_in),
    .FIFO_RD_CLK (FIFO_RD_CLK_in),
    .FIFO_RD_EN (FIFO_RD_EN_in),
    .IFD_CE (IFD_CE_in),
    .OFD_CE (OFD_CE_in),
    .RX2TX_CASC_RETURN_IN (RX2TX_CASC_RETURN_IN_in),
    .RX_BIT_CTRL_IN (RX_BIT_CTRL_IN_in),
    .RX_CE (RX_CE_in),
    .RX_CLK (RX_CLK_in),
    .RX_CLKDIV (RX_CLKDIV_in),
    .RX_CLK_C (RX_CLK_C_in),
    .RX_CLK_C_B (RX_CLK_C_B_in),
    .RX_CNTVALUEIN (RX_CNTVALUEIN_in),
    .RX_DATAIN1 (RX_DATAIN1_in),
    .RX_EN_VTC (RX_EN_VTC_in),
    .RX_INC (RX_INC_in),
    .RX_LOAD (RX_LOAD_in),
    .RX_RST (RX_RST_in),
    .RX_RST_DLY (RX_RST_DLY_in),
    .T (T_in),
    .TBYTE_IN (TBYTE_IN_in),
    .TX2RX_CASC_IN (TX2RX_CASC_IN_in),
    .TX_BIT_CTRL_IN (TX_BIT_CTRL_IN_in),
    .TX_CE (TX_CE_in),
    .TX_CLK (TX_CLK_in),
    .TX_CNTVALUEIN (TX_CNTVALUEIN_in),
    .TX_EN_VTC (TX_EN_VTC_in),
    .TX_INC (TX_INC_in),
    .TX_LOAD (TX_LOAD_in),
    .TX_OCLK (TX_OCLK_in),
    .TX_OCLKDIV (TX_OCLKDIV_in),
    .TX_RST (TX_RST_in),
    .TX_RST_DLY (TX_RST_DLY_in),
    .SIM_IDELAY_DATAIN0(IDELAY_DATAIN0_out),
    .SIM_IDELAY_DATAOUT(IDELAY_DATAOUT_out),
    .SIM_ODELAY_DATAIN0(ODELAY_DATAIN0_out),
    .SIM_ODELAY_DATAOUT(ODELAY_DATAOUT_out),
    .GSR (glblGSR)
  );
end 
endgenerate

`ifdef XIL_TIMING
  wire rx_clk_en_n;
  wire rx_clk_en_p;
  wire tx_clk_en_n;
  wire tx_clk_en_p;
  
  assign rx_clk_en_n =  IS_RX_CLK_INVERTED_BIN;
  assign rx_clk_en_p = ~IS_RX_CLK_INVERTED_BIN;
  assign tx_clk_en_n =  IS_TX_CLK_INVERTED_BIN;
  assign tx_clk_en_p = ~IS_TX_CLK_INVERTED_BIN;
`endif

  specify
    (DATAIN => Q[4]) = (0:0:0, 0:0:0);
    (DATAIN => Q[5]) = (0:0:0, 0:0:0);
    (DATAIN => RX_BIT_CTRL_OUT[9]) = (0:0:0, 0:0:0);
    (D[0] => O) = (0:0:0, 0:0:0);
    (D[1] => T_OUT) = (0:0:0, 0:0:0);
    (FIFO_RD_CLK => FIFO_EMPTY) = (100:100:100, 100:100:100);
    (FIFO_RD_CLK => Q[0]) = (100:100:100, 100:100:100);
    (FIFO_RD_CLK => Q[1]) = (100:100:100, 100:100:100);
    (FIFO_RD_CLK => Q[2]) = (100:100:100, 100:100:100);
    (FIFO_RD_CLK => Q[3]) = (100:100:100, 100:100:100);
    (FIFO_RD_CLK => Q[4]) = (100:100:100, 100:100:100);
    (FIFO_RD_CLK => Q[5]) = (100:100:100, 100:100:100);
    (FIFO_RD_CLK => Q[6]) = (100:100:100, 100:100:100);
    (FIFO_RD_CLK => Q[7]) = (100:100:100, 100:100:100);
    (RX_BIT_CTRL_IN[20] => FIFO_WRCLK_OUT) = (0:0:0, 0:0:0);
    (RX_CLK => RX_CNTVALUEOUT[0]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_CNTVALUEOUT[1]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_CNTVALUEOUT[2]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_CNTVALUEOUT[3]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_CNTVALUEOUT[4]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_CNTVALUEOUT[5]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_CNTVALUEOUT[6]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_CNTVALUEOUT[7]) = (100:100:100, 100:100:100);
    (RX_CLK => RX_CNTVALUEOUT[8]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_CNTVALUEOUT[0]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_CNTVALUEOUT[1]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_CNTVALUEOUT[2]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_CNTVALUEOUT[3]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_CNTVALUEOUT[4]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_CNTVALUEOUT[5]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_CNTVALUEOUT[6]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_CNTVALUEOUT[7]) = (100:100:100, 100:100:100);
    (TX_CLK => TX_CNTVALUEOUT[8]) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $period (negedge FIFO_RD_CLK, 0:0:0, notifier);
    $period (negedge RX_BIT_CTRL_IN[20], 0:0:0, notifier);
    $period (negedge RX_CLK, 0:0:0, notifier);
    $period (negedge TX_BIT_CTRL_IN[25], 0:0:0, notifier);
    $period (negedge TX_BIT_CTRL_IN[26], 0:0:0, notifier);
    $period (negedge TX_CLK, 0:0:0, notifier);
    $period (posedge FIFO_RD_CLK, 0:0:0, notifier);
    $period (posedge RX_BIT_CTRL_IN[20], 0:0:0, notifier);
    $period (posedge RX_CLK, 0:0:0, notifier);
    $period (posedge TX_BIT_CTRL_IN[25], 0:0:0, notifier);
    $period (posedge TX_BIT_CTRL_IN[26], 0:0:0, notifier);
    $period (posedge TX_CLK, 0:0:0, notifier);
    $setuphold (negedge RX_CLK, negedge RX_CE, 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CE_delay);
    $setuphold (negedge RX_CLK, negedge RX_CNTVALUEIN[0], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[0]);
    $setuphold (negedge RX_CLK, negedge RX_CNTVALUEIN[1], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[1]);
    $setuphold (negedge RX_CLK, negedge RX_CNTVALUEIN[2], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[2]);
    $setuphold (negedge RX_CLK, negedge RX_CNTVALUEIN[3], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[3]);
    $setuphold (negedge RX_CLK, negedge RX_CNTVALUEIN[4], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[4]);
    $setuphold (negedge RX_CLK, negedge RX_CNTVALUEIN[5], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[5]);
    $setuphold (negedge RX_CLK, negedge RX_CNTVALUEIN[6], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[6]);
    $setuphold (negedge RX_CLK, negedge RX_CNTVALUEIN[7], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[7]);
    $setuphold (negedge RX_CLK, negedge RX_CNTVALUEIN[8], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[8]);
    $setuphold (negedge RX_CLK, negedge RX_INC, 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_INC_delay);
    $setuphold (negedge RX_CLK, negedge RX_LOAD, 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_LOAD_delay);
    $setuphold (negedge RX_CLK, posedge RX_CE, 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CE_delay);
    $setuphold (negedge RX_CLK, posedge RX_CNTVALUEIN[0], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[0]);
    $setuphold (negedge RX_CLK, posedge RX_CNTVALUEIN[1], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[1]);
    $setuphold (negedge RX_CLK, posedge RX_CNTVALUEIN[2], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[2]);
    $setuphold (negedge RX_CLK, posedge RX_CNTVALUEIN[3], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[3]);
    $setuphold (negedge RX_CLK, posedge RX_CNTVALUEIN[4], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[4]);
    $setuphold (negedge RX_CLK, posedge RX_CNTVALUEIN[5], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[5]);
    $setuphold (negedge RX_CLK, posedge RX_CNTVALUEIN[6], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[6]);
    $setuphold (negedge RX_CLK, posedge RX_CNTVALUEIN[7], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[7]);
    $setuphold (negedge RX_CLK, posedge RX_CNTVALUEIN[8], 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_CNTVALUEIN_delay[8]);
    $setuphold (negedge RX_CLK, posedge RX_INC, 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_INC_delay);
    $setuphold (negedge RX_CLK, posedge RX_LOAD, 0:0:0, 0:0:0, notifier, rx_clk_en_n, rx_clk_en_n, RX_CLK_delay, RX_LOAD_delay);
    $setuphold (negedge TX_BIT_CTRL_IN[25], negedge D[0], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[0]);
    $setuphold (negedge TX_BIT_CTRL_IN[25], negedge D[1], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[1]);
    $setuphold (negedge TX_BIT_CTRL_IN[25], negedge D[2], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[2]);
    $setuphold (negedge TX_BIT_CTRL_IN[25], negedge D[3], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[3]);
    $setuphold (negedge TX_BIT_CTRL_IN[25], posedge D[0], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[0]);
    $setuphold (negedge TX_BIT_CTRL_IN[25], posedge D[1], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[1]);
    $setuphold (negedge TX_BIT_CTRL_IN[25], posedge D[2], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[2]);
    $setuphold (negedge TX_BIT_CTRL_IN[25], posedge D[3], 0:0:0, 0:0:0, notifier, , , TX_BIT_CTRL_IN_delay[25], D_delay[3]);
    $setuphold (negedge TX_CLK, negedge TX_CE, 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CE_delay);
    $setuphold (negedge TX_CLK, negedge TX_CNTVALUEIN[0], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[0]);
    $setuphold (negedge TX_CLK, negedge TX_CNTVALUEIN[1], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[1]);
    $setuphold (negedge TX_CLK, negedge TX_CNTVALUEIN[2], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[2]);
    $setuphold (negedge TX_CLK, negedge TX_CNTVALUEIN[3], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[3]);
    $setuphold (negedge TX_CLK, negedge TX_CNTVALUEIN[4], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[4]);
    $setuphold (negedge TX_CLK, negedge TX_CNTVALUEIN[5], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[5]);
    $setuphold (negedge TX_CLK, negedge TX_CNTVALUEIN[6], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[6]);
    $setuphold (negedge TX_CLK, negedge TX_CNTVALUEIN[7], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[7]);
    $setuphold (negedge TX_CLK, negedge TX_CNTVALUEIN[8], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[8]);
    $setuphold (negedge TX_CLK, negedge TX_INC, 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_INC_delay);
    $setuphold (negedge TX_CLK, negedge TX_LOAD, 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_LOAD_delay);
    $setuphold (negedge TX_CLK, posedge TX_CE, 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CE_delay);
    $setuphold (negedge TX_CLK, posedge TX_CNTVALUEIN[0], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[0]);
    $setuphold (negedge TX_CLK, posedge TX_CNTVALUEIN[1], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[1]);
    $setuphold (negedge TX_CLK, posedge TX_CNTVALUEIN[2], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[2]);
    $setuphold (negedge TX_CLK, posedge TX_CNTVALUEIN[3], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[3]);
    $setuphold (negedge TX_CLK, posedge TX_CNTVALUEIN[4], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[4]);
    $setuphold (negedge TX_CLK, posedge TX_CNTVALUEIN[5], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[5]);
    $setuphold (negedge TX_CLK, posedge TX_CNTVALUEIN[6], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[6]);
    $setuphold (negedge TX_CLK, posedge TX_CNTVALUEIN[7], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[7]);
    $setuphold (negedge TX_CLK, posedge TX_CNTVALUEIN[8], 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_CNTVALUEIN_delay[8]);
    $setuphold (negedge TX_CLK, posedge TX_INC, 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_INC_delay);
    $setuphold (negedge TX_CLK, posedge TX_LOAD, 0:0:0, 0:0:0, notifier, tx_clk_en_n, tx_clk_en_n, TX_CLK_delay, TX_LOAD_delay);
    $setuphold (posedge FIFO_RD_CLK, negedge FIFO_RD_EN, 0:0:0, 0:0:0, notifier, , , FIFO_RD_CLK_delay, FIFO_RD_EN_delay);
    $setuphold (posedge FIFO_RD_CLK, posedge FIFO_RD_EN, 0:0:0, 0:0:0, notifier, , , FIFO_RD_CLK_delay, FIFO_RD_EN_delay);
    $setuphold (posedge RX_CLK, negedge RX_CE, 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CE_delay);
    $setuphold (posedge RX_CLK, negedge RX_CNTVALUEIN[0], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[0]);
    $setuphold (posedge RX_CLK, negedge RX_CNTVALUEIN[1], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[1]);
    $setuphold (posedge RX_CLK, negedge RX_CNTVALUEIN[2], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[2]);
    $setuphold (posedge RX_CLK, negedge RX_CNTVALUEIN[3], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[3]);
    $setuphold (posedge RX_CLK, negedge RX_CNTVALUEIN[4], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[4]);
    $setuphold (posedge RX_CLK, negedge RX_CNTVALUEIN[5], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[5]);
    $setuphold (posedge RX_CLK, negedge RX_CNTVALUEIN[6], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[6]);
    $setuphold (posedge RX_CLK, negedge RX_CNTVALUEIN[7], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[7]);
    $setuphold (posedge RX_CLK, negedge RX_CNTVALUEIN[8], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[8]);
    $setuphold (posedge RX_CLK, negedge RX_INC, 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_INC_delay);
    $setuphold (posedge RX_CLK, negedge RX_LOAD, 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_LOAD_delay);
    $setuphold (posedge RX_CLK, posedge RX_CE, 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CE_delay);
    $setuphold (posedge RX_CLK, posedge RX_CNTVALUEIN[0], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[0]);
    $setuphold (posedge RX_CLK, posedge RX_CNTVALUEIN[1], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[1]);
    $setuphold (posedge RX_CLK, posedge RX_CNTVALUEIN[2], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[2]);
    $setuphold (posedge RX_CLK, posedge RX_CNTVALUEIN[3], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[3]);
    $setuphold (posedge RX_CLK, posedge RX_CNTVALUEIN[4], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[4]);
    $setuphold (posedge RX_CLK, posedge RX_CNTVALUEIN[5], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[5]);
    $setuphold (posedge RX_CLK, posedge RX_CNTVALUEIN[6], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[6]);
    $setuphold (posedge RX_CLK, posedge RX_CNTVALUEIN[7], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[7]);
    $setuphold (posedge RX_CLK, posedge RX_CNTVALUEIN[8], 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_CNTVALUEIN_delay[8]);
    $setuphold (posedge RX_CLK, posedge RX_INC, 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_INC_delay);
    $setuphold (posedge RX_CLK, posedge RX_LOAD, 0:0:0, 0:0:0, notifier, rx_clk_en_p, rx_clk_en_p, RX_CLK_delay, RX_LOAD_delay);
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
    $setuphold (posedge TX_CLK, negedge TX_CE, 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CE_delay);
    $setuphold (posedge TX_CLK, negedge TX_CNTVALUEIN[0], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[0]);
    $setuphold (posedge TX_CLK, negedge TX_CNTVALUEIN[1], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[1]);
    $setuphold (posedge TX_CLK, negedge TX_CNTVALUEIN[2], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[2]);
    $setuphold (posedge TX_CLK, negedge TX_CNTVALUEIN[3], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[3]);
    $setuphold (posedge TX_CLK, negedge TX_CNTVALUEIN[4], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[4]);
    $setuphold (posedge TX_CLK, negedge TX_CNTVALUEIN[5], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[5]);
    $setuphold (posedge TX_CLK, negedge TX_CNTVALUEIN[6], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[6]);
    $setuphold (posedge TX_CLK, negedge TX_CNTVALUEIN[7], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[7]);
    $setuphold (posedge TX_CLK, negedge TX_CNTVALUEIN[8], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[8]);
    $setuphold (posedge TX_CLK, negedge TX_INC, 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_INC_delay);
    $setuphold (posedge TX_CLK, negedge TX_LOAD, 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_LOAD_delay);
    $setuphold (posedge TX_CLK, posedge TX_CE, 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CE_delay);
    $setuphold (posedge TX_CLK, posedge TX_CNTVALUEIN[0], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[0]);
    $setuphold (posedge TX_CLK, posedge TX_CNTVALUEIN[1], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[1]);
    $setuphold (posedge TX_CLK, posedge TX_CNTVALUEIN[2], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[2]);
    $setuphold (posedge TX_CLK, posedge TX_CNTVALUEIN[3], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[3]);
    $setuphold (posedge TX_CLK, posedge TX_CNTVALUEIN[4], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[4]);
    $setuphold (posedge TX_CLK, posedge TX_CNTVALUEIN[5], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[5]);
    $setuphold (posedge TX_CLK, posedge TX_CNTVALUEIN[6], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[6]);
    $setuphold (posedge TX_CLK, posedge TX_CNTVALUEIN[7], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[7]);
    $setuphold (posedge TX_CLK, posedge TX_CNTVALUEIN[8], 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_CNTVALUEIN_delay[8]);
    $setuphold (posedge TX_CLK, posedge TX_INC, 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_INC_delay);
    $setuphold (posedge TX_CLK, posedge TX_LOAD, 0:0:0, 0:0:0, notifier, tx_clk_en_p, tx_clk_en_p, TX_CLK_delay, TX_LOAD_delay);
    $width (negedge FIFO_RD_CLK, 0:0:0, 0, notifier);
    $width (negedge RX_BIT_CTRL_IN[20], 0:0:0, 0, notifier);
    $width (negedge RX_CLK, 0:0:0, 0, notifier);
    $width (negedge TX_BIT_CTRL_IN[25], 0:0:0, 0, notifier);
    $width (negedge TX_BIT_CTRL_IN[26], 0:0:0, 0, notifier);
    $width (negedge TX_CLK, 0:0:0, 0, notifier);
    $width (posedge FIFO_RD_CLK, 0:0:0, 0, notifier);
    $width (posedge RX_BIT_CTRL_IN[20], 0:0:0, 0, notifier);
    $width (posedge RX_CLK, 0:0:0, 0, notifier);
    $width (posedge TX_BIT_CTRL_IN[25], 0:0:0, 0, notifier);
    $width (posedge TX_BIT_CTRL_IN[26], 0:0:0, 0, notifier);
    $width (posedge TX_CLK, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
