///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2017 Xilinx, Inc.
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
// \   \   \/      Version     : 2018.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        Input Fixed or Variable Delay Element
// /___/   /\      Filename    : IDELAYE3.v
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

module IDELAYE3 #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter CASCADE = "NONE",
  parameter DELAY_FORMAT = "TIME",
  parameter DELAY_SRC = "IDATAIN",
  parameter DELAY_TYPE = "FIXED",
  parameter integer DELAY_VALUE = 0,
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [0:0] IS_RST_INVERTED = 1'b0,
  parameter LOOPBACK = "FALSE",
  parameter real REFCLK_FREQUENCY = 300.0,
  parameter SIM_DEVICE = "ULTRASCALE",
  parameter real SIM_VERSION = 2.0,
  parameter UPDATE_MODE = "ASYNC"
)(
  output CASC_OUT,
  output [8:0] CNTVALUEOUT,
  output DATAOUT,

  input CASC_IN,
  input CASC_RETURN,
  input CE,
  input CLK,
  input [8:0] CNTVALUEIN,
  input DATAIN,
  input EN_VTC,
  input IDATAIN,
  input INC,
  input LOAD,
  input RST
);

// define constants
  localparam MODULE_NAME = "IDELAYE3";
  localparam in_delay    = 0;
  localparam out_delay   = 0;
  localparam inclk_delay    = 0;
  localparam outclk_delay   = 0;

// Parameter encodings and registers
  localparam CASCADE_MASTER = 1;
  localparam CASCADE_NONE = 0;
  localparam CASCADE_SLAVE_END = 2;
  localparam CASCADE_SLAVE_MIDDLE = 3;
  localparam DELAY_FORMAT_COUNT = 1;
  localparam DELAY_FORMAT_TIME = 0;
  localparam DELAY_SRC_DATAIN = 1;
  localparam DELAY_SRC_IDATAIN = 0;
  localparam DELAY_TYPE_FIXED = 0;
  localparam DELAY_TYPE_VARIABLE = 1;
  localparam DELAY_TYPE_VAR_LOAD = 2;
  localparam LOOPBACK_FALSE = 0;
  localparam LOOPBACK_TRUE = 1;
  localparam SIM_DEVICE_ULTRASCALE = 0;
  localparam SIM_DEVICE_ULTRASCALE_PLUS = 1;
  localparam SIM_DEVICE_ULTRASCALE_PLUS_ES1 = 2;
  localparam SIM_DEVICE_ULTRASCALE_PLUS_ES2 = 3;
  localparam UPDATE_MODE_ASYNC = 0;
  localparam UPDATE_MODE_MANUAL = 1;
  localparam UPDATE_MODE_SYNC = 2;

  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "IDELAYE3_dr.v"
`else
  localparam [96:1] CASCADE_REG = CASCADE;
  localparam [40:1] DELAY_FORMAT_REG = DELAY_FORMAT;
  localparam [56:1] DELAY_SRC_REG = DELAY_SRC;
  localparam [64:1] DELAY_TYPE_REG = DELAY_TYPE;
  localparam [31:0] DELAY_VALUE_REG = DELAY_VALUE;
  localparam [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
  localparam [0:0] IS_RST_INVERTED_REG = IS_RST_INVERTED;
  localparam [40:1] LOOPBACK_REG = LOOPBACK;
  localparam real REFCLK_FREQUENCY_REG = REFCLK_FREQUENCY;
  localparam [152:1] SIM_DEVICE_REG = SIM_DEVICE;
  localparam real SIM_VERSION_REG = SIM_VERSION;
  localparam [48:1] UPDATE_MODE_REG = UPDATE_MODE;
`endif

  wire [1:0] CASCADE_BIN;
  wire DELAY_FORMAT_BIN;
  wire DELAY_SRC_BIN;
  wire [1:0] DELAY_TYPE_BIN;
  wire [10:0] DELAY_VALUE_BIN;
  wire LOOPBACK_BIN;
  wire [63:0] REFCLK_FREQUENCY_BIN;
  wire [1:0] SIM_DEVICE_BIN;
  wire [63:0] SIM_VERSION_BIN;
  wire [1:0] UPDATE_MODE_BIN;

  reg attr_test;
  reg attr_err;
  tri0 glblGSR = glbl.GSR;

  wire CASC_IN_in;
  wire CASC_RETURN_in;
  wire CE_in;
  wire CLK_in;
  wire DATAIN_in;
  wire EN_VTC_in;
  wire IDATAIN_in;
  wire INC_in;
  wire LOAD_in;
  wire RST_in;
  wire [8:0] CNTVALUEIN_in;

  wire CASC_IN_delay;
  wire CASC_RETURN_delay;
  wire CE_delay;
  wire CLK_delay;
  wire DATAIN_delay;
  wire EN_VTC_delay;
  wire IDATAIN_delay;
  wire INC_delay;
  wire LOAD_delay;
  wire RST_delay;
  wire [8:0] CNTVALUEIN_delay;

  reg CASC_OUT_out;
  reg DATAOUT_out;
  reg [8:0] CNTVALUEOUT_out;

  wire CASC_OUT_delay;
  wire DATAOUT_delay;
  wire [8:0] CNTVALUEOUT_delay;

  assign #(out_delay) CASC_OUT = CASC_OUT_delay;
  assign #(out_delay) CNTVALUEOUT = (EN_VTC_in === 1'b1) ? 9'bxxxxxxxxx : CNTVALUEOUT_delay;
  assign #(out_delay) DATAOUT = DATAOUT_delay;
  
`ifndef XIL_TIMING // inputs with timing checks
  assign #(inclk_delay) CLK_delay = CLK;

  assign #(in_delay) CE_delay = CE;
  assign #(in_delay) CNTVALUEIN_delay = CNTVALUEIN;
  assign #(in_delay) INC_delay = INC;
  assign #(in_delay) LOAD_delay = LOAD;
`endif //  `ifndef XIL_TIMING
// inputs with no timing checks

  assign #(in_delay) RST_delay = RST;
  assign #(in_delay) CASC_IN_delay = CASC_IN;
  assign #(in_delay) CASC_RETURN_delay = CASC_RETURN;
  assign #(in_delay) DATAIN_delay = DATAIN;
  assign #(in_delay) EN_VTC_delay = EN_VTC;
  assign #(in_delay) IDATAIN_delay = IDATAIN;

  assign CASC_OUT_delay = CASC_OUT_out;
  assign CNTVALUEOUT_delay = CNTVALUEOUT_out;
  assign DATAOUT_delay = DATAOUT_out;

  assign CASC_IN_in = CASC_IN_delay;
  assign CASC_RETURN_in = CASC_RETURN_delay;
  assign CE_in = CE_delay;
  assign CLK_in = CLK_delay ^ IS_CLK_INVERTED_REG;
  assign CNTVALUEIN_in[0] = (CNTVALUEIN[0] === 1'bz) || CNTVALUEIN_delay[0]; // rv 1
  assign CNTVALUEIN_in[1] = (CNTVALUEIN[1] === 1'bz) || CNTVALUEIN_delay[1]; // rv 1
  assign CNTVALUEIN_in[2] = (CNTVALUEIN[2] === 1'bz) || CNTVALUEIN_delay[2]; // rv 1
  assign CNTVALUEIN_in[3] = (CNTVALUEIN[3] === 1'bz) || CNTVALUEIN_delay[3]; // rv 1
  assign CNTVALUEIN_in[4] = (CNTVALUEIN[4] === 1'bz) || CNTVALUEIN_delay[4]; // rv 1
  assign CNTVALUEIN_in[5] = (CNTVALUEIN[5] === 1'bz) || CNTVALUEIN_delay[5]; // rv 1
  assign CNTVALUEIN_in[6] = (CNTVALUEIN[6] === 1'bz) || CNTVALUEIN_delay[6]; // rv 1
  assign CNTVALUEIN_in[7] = (CNTVALUEIN[7] === 1'bz) || CNTVALUEIN_delay[7]; // rv 1
  assign CNTVALUEIN_in[8] = (CNTVALUEIN[8] === 1'bz) || CNTVALUEIN_delay[8]; // rv 1
  assign DATAIN_in = DATAIN_delay;
  assign EN_VTC_in = EN_VTC_delay;
  assign IDATAIN_in = IDATAIN_delay;
  assign INC_in = INC_delay;
  assign LOAD_in = LOAD_delay;
  assign RST_in = RST_delay ^ IS_RST_INVERTED_REG;

`ifndef XIL_XECLIB
  initial begin
  trig_attr = 1'b0;
  `ifdef XIL_ATTR_TEST
    attr_test = 1'b1;
  `else
    attr_test = 1'b0;
  `endif
    attr_err = 1'b0;
    #1;
    trig_attr = ~trig_attr;
  end
`endif

  assign CASCADE_BIN = 
    (CASCADE_REG == "NONE") ? CASCADE_NONE :
    (CASCADE_REG == "MASTER") ? CASCADE_MASTER :
    (CASCADE_REG == "SLAVE_END") ? CASCADE_SLAVE_END :
    (CASCADE_REG == "SLAVE_MIDDLE") ? CASCADE_SLAVE_MIDDLE :
    CASCADE_NONE;

  assign DELAY_FORMAT_BIN = 
    (DELAY_FORMAT_REG == "TIME") ? DELAY_FORMAT_TIME :
    (DELAY_FORMAT_REG == "COUNT") ? DELAY_FORMAT_COUNT :
    DELAY_FORMAT_TIME;

  assign DELAY_SRC_BIN = 
    (DELAY_SRC_REG == "IDATAIN") ? DELAY_SRC_IDATAIN :
    (DELAY_SRC_REG == "DATAIN") ? DELAY_SRC_DATAIN :
    DELAY_SRC_IDATAIN;

  assign DELAY_TYPE_BIN = 
    (DELAY_TYPE_REG == "FIXED") ? DELAY_TYPE_FIXED :
    (DELAY_TYPE_REG == "VARIABLE") ? DELAY_TYPE_VARIABLE :
    (DELAY_TYPE_REG == "VAR_LOAD") ? DELAY_TYPE_VAR_LOAD :
    DELAY_TYPE_FIXED;

  assign DELAY_VALUE_BIN = DELAY_VALUE_REG[10:0];
  
  assign LOOPBACK_BIN =
      (LOOPBACK_REG == "FALSE") ? LOOPBACK_FALSE :
      (LOOPBACK_REG == "TRUE") ? LOOPBACK_TRUE :
       LOOPBACK_FALSE;
  
  assign REFCLK_FREQUENCY_BIN = REFCLK_FREQUENCY_REG * 1000;
  
  assign SIM_DEVICE_BIN =
      (SIM_DEVICE_REG == "ULTRASCALE") ? SIM_DEVICE_ULTRASCALE :
      (SIM_DEVICE_REG == "ULTRASCALE_PLUS") ? SIM_DEVICE_ULTRASCALE_PLUS :
      (SIM_DEVICE_REG == "ULTRASCALE_PLUS_ES1") ? SIM_DEVICE_ULTRASCALE_PLUS_ES1 :
      (SIM_DEVICE_REG == "ULTRASCALE_PLUS_ES2") ? SIM_DEVICE_ULTRASCALE_PLUS_ES2 :
       SIM_DEVICE_ULTRASCALE;
  
  assign SIM_VERSION_BIN = SIM_VERSION_REG * 1000;
  
  assign UPDATE_MODE_BIN =
      (UPDATE_MODE_REG == "ASYNC") ? UPDATE_MODE_ASYNC :
      (UPDATE_MODE_REG == "MANUAL") ? UPDATE_MODE_MANUAL :
      (UPDATE_MODE_REG == "SYNC") ? UPDATE_MODE_SYNC :
       UPDATE_MODE_ASYNC;

  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((CASCADE_REG != "NONE") &&
         (CASCADE_REG != "MASTER") &&
         (CASCADE_REG != "SLAVE_END") &&
         (CASCADE_REG != "SLAVE_MIDDLE"))) begin
      $display("Error: [Unisim %s-101] CASCADE attribute is set to %s.  Legal values for this attribute are NONE, MASTER, SLAVE_END or SLAVE_MIDDLE. Instance: %m", MODULE_NAME, CASCADE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((DELAY_FORMAT_REG != "TIME") &&
         (DELAY_FORMAT_REG != "COUNT"))) begin
      $display("Error: [Unisim %s-102] DELAY_FORMAT attribute is set to %s.  Legal values for this attribute are TIME or COUNT. Instance: %m", MODULE_NAME, DELAY_FORMAT_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((DELAY_SRC_REG != "IDATAIN") &&
         (DELAY_SRC_REG != "DATAIN"))) begin
      $display("Error: [Unisim %s-103] DELAY_SRC attribute is set to %s.  Legal values for this attribute are IDATAIN or DATAIN. Instance: %m", MODULE_NAME, DELAY_SRC_REG);
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
        (SIM_DEVICE_REG != "ULTRASCALE" && ((DELAY_VALUE_REG < 0) || (DELAY_VALUE_REG > 1100)))) begin
      $display("Error: [Unisim %s-105] DELAY_VALUE attribute is set to %d.  Legal values for this attribute are 0 to 1100. Instance: %m", MODULE_NAME, DELAY_VALUE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        (SIM_DEVICE_REG == "ULTRASCALE" && ((DELAY_VALUE_REG < 0) || (DELAY_VALUE_REG > 1250)))) begin
      $display("Error: [Unisim %s-105] DELAY_VALUE attribute is set to %d.  Legal values for this attribute are 0 to 1250. Instance: %m", MODULE_NAME, DELAY_VALUE_REG);
      attr_err = 1'b1;
    end
 
    if ((attr_test == 1'b1) ||
        ((LOOPBACK_REG != "FALSE") &&
         (LOOPBACK_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-108] LOOPBACK attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, LOOPBACK_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        (SIM_DEVICE_REG != "ULTRASCALE" && (REFCLK_FREQUENCY_REG < 300.0 || REFCLK_FREQUENCY_REG > 2667.0))) begin
      $display("Error: [Unisim %s-109] REFCLK_FREQUENCY attribute is set to %f.  Legal values for this attribute are 300.0 to 2667.0. Instance: %m", MODULE_NAME, REFCLK_FREQUENCY_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (SIM_DEVICE_REG == "ULTRASCALE" && (REFCLK_FREQUENCY_REG < 200.0 || REFCLK_FREQUENCY_REG > 2400.0))) begin
      $display("Error: [Unisim %s-109] REFCLK_FREQUENCY attribute is set to %f.  Legal values for this attribute are 200.0 to 2400.0. Instance: %m", MODULE_NAME, REFCLK_FREQUENCY_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2"))) begin
      $display("Error: [Unisim %s-110] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE, ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1 or ULTRASCALE_PLUS_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
       ((SIM_VERSION_REG != 2.0) &&
        (SIM_VERSION_REG != 1.0))) begin
      $display("Error: [Unisim %s-111] SIM_VERSION attribute is set to %f.  Legal values for this attribute are 2.0 or 1.0. Instance: %m", MODULE_NAME, SIM_VERSION_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((UPDATE_MODE_REG != "ASYNC") &&
         (UPDATE_MODE_REG != "MANUAL") &&
         (UPDATE_MODE_REG != "SYNC"))) begin
      $display("Error: [Unisim %s-112] UPDATE_MODE attribute is set to %s.  Legal values for this attribute are ASYNC, MANUAL or SYNC. Instance: %m", MODULE_NAME, UPDATE_MODE_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
    end

`ifdef XIL_TIMING
  reg notifier;
`endif

// begin behavioral model

  localparam MAX_DELAY_COUNT = 511; 
  localparam MIN_DELAY_COUNT = 0;

  integer PER_BIT_FINE_DELAY;
  integer PER_BIT_MEDIUM_DELAY;
  integer INTRINSIC_FINE_DELAY;
  integer INTRINSIC_MEDIUM_DELAY;
  integer IDATAIN_INTRINSIC_DELAY;
  integer DATAIN_INTRINSIC_DELAY;
  integer CASC_IN_INTRINSIC_DELAY;
  integer CASC_RET_INTRINSIC_DELAY;
  integer DATA_OUT_INTRINSIC_DELAY;
  integer CASC_OUT_INTRINSIC_DELAY;

  reg [17:0] gen_mc_fixed_dly_ratio;
  reg tap_out;
  reg clk_smux;
  reg data_mux;
  reg data_mux_sync;
  reg data_mux_sync1;
  reg data_mux_sync2;
  reg data_mux_sync3;
  reg data_mux_sync4;
  reg cdataout_pre;
  reg RST_sync1;
  reg RST_sync2;
  reg RST_sync3;
  reg [8:0] idelay_count_async;
  reg [8:0] idelay_count_sync;
  reg [8:0] cntvalue_updated;
  reg [8:0] cntvalue_updated_sync;
  reg [8:0] cntvalue_updated_async;
  reg [8:0] idelay_count_pre;
  reg [8:0] CNTVALUEIN_INTEGER;
  time delay_value;

  initial begin
    case (SIM_DEVICE)
      "ULTRASCALE" : begin
        PER_BIT_FINE_DELAY = 5;
        PER_BIT_MEDIUM_DELAY = 40;
        INTRINSIC_FINE_DELAY = 75;
        INTRINSIC_MEDIUM_DELAY = 40;
        IDATAIN_INTRINSIC_DELAY = 20;
        DATAIN_INTRINSIC_DELAY = 60;
        CASC_IN_INTRINSIC_DELAY = 60;
        CASC_RET_INTRINSIC_DELAY = 60;
        DATA_OUT_INTRINSIC_DELAY = 25;
        CASC_OUT_INTRINSIC_DELAY = 80;
      end
      "ULTRASCALE_PLUS","ULTRASCALE_PLUS_ES1","ULTRASCALE_PLUS_ES2" : begin
        PER_BIT_FINE_DELAY = 4;
        PER_BIT_MEDIUM_DELAY = 32;
        INTRINSIC_FINE_DELAY = 60;
        INTRINSIC_MEDIUM_DELAY = 32;
        IDATAIN_INTRINSIC_DELAY = 15;
        DATAIN_INTRINSIC_DELAY = 32;
        CASC_IN_INTRINSIC_DELAY = 32;
        CASC_RET_INTRINSIC_DELAY = 32;
        DATA_OUT_INTRINSIC_DELAY = 20;
        CASC_OUT_INTRINSIC_DELAY = 45;
      end
      default : begin
        PER_BIT_FINE_DELAY = 5;
        PER_BIT_MEDIUM_DELAY = 40;
        INTRINSIC_FINE_DELAY = 75;
        INTRINSIC_MEDIUM_DELAY = 40;
        IDATAIN_INTRINSIC_DELAY = 20;
        DATAIN_INTRINSIC_DELAY = 60;
        CASC_IN_INTRINSIC_DELAY = 60;
        CASC_RET_INTRINSIC_DELAY = 60;
        DATA_OUT_INTRINSIC_DELAY = 25;
        CASC_OUT_INTRINSIC_DELAY = 80;
      end
    endcase
    CNTVALUEOUT_out = 9'b0;
    DATAOUT_out = 1'b0;
    CASC_OUT_out = 1'b0;
    cdataout_pre = 1'b0;
  end

   always @(RST_in) begin
     if (RST_in === 1'b1 && DELAY_FORMAT_REG == "TIME")
       $display("Warning: [Unisim %s-1] Ultrascale IDELAYCTRL and I/ODELAYE3, RST simulation behaviour may not match hardware behaviour when DELAY_FORMAT = TIME, if SelectIO User Guide recommendation for I/ODELAY connections or reset sequence are not followed. For more information, refer to the Select IO Userguide Instance: %m", MODULE_NAME);
   end

  always @ (trig_attr) begin
    #1;
    if (DELAY_FORMAT_BIN == DELAY_FORMAT_TIME) begin
      if ((DELAY_VALUE_REG == 0) || (REFCLK_FREQUENCY_REG == 0)) begin
        idelay_count_pre = 0;
        cntvalue_updated = idelay_count_pre;
      end else begin  
        idelay_count_pre = DELAY_VALUE_REG/PER_BIT_FINE_DELAY;
        cntvalue_updated = idelay_count_pre;
      end  
    end else if (DELAY_FORMAT_BIN == DELAY_FORMAT_COUNT) begin
      idelay_count_pre = DELAY_VALUE_REG;
      cntvalue_updated = idelay_count_pre;
    end
  end

//----------------------------------------------------------------------
//-------------------------------  Output ------------------------------
//----------------------------------------------------------------------
  always @(tap_out) begin
    DATAOUT_out <= #(DATA_OUT_INTRINSIC_DELAY) tap_out;
  end

  always @(cdataout_pre) begin
    CASC_OUT_out <= #(CASC_OUT_INTRINSIC_DELAY) cdataout_pre;
  end

//----------------------------------------------------------------------
//-------------------------------  Input -------------------------------
//----------------------------------------------------------------------

//*** GLOBAL hidden GSR pin
  always @(glblGSR or RST_in) begin
    if (glblGSR == 1'b1 || RST_in == 1'b1) begin
//      assign idelay_count_sync = idelay_count_pre;
      assign idelay_count_async = idelay_count_pre;
      assign cntvalue_updated_sync = idelay_count_pre;
      assign cntvalue_updated_async = idelay_count_pre;
    end else if (glblGSR == 1'b0 || RST_in == 1'b0) begin
//      deassign idelay_count_sync;
      deassign idelay_count_async;
      deassign cntvalue_updated_sync;
      deassign cntvalue_updated_async;
    end
  end   

//----------------------------------------------------------------------
//------------------------      CNTVALUEOUT        ---------------------
//----------------------------------------------------------------------
//    always @(idelay_count_sync or idelay_count_async or cntvalue_updated_async or cntvalue_updated_sync or UPDATE_MODE_REG) begin
    always @(idelay_count_async or cntvalue_updated_async or cntvalue_updated_sync or UPDATE_MODE_REG) begin
     case (UPDATE_MODE_REG)
       "SYNC" : begin
         CNTVALUEOUT_out = idelay_count_async;
         cntvalue_updated = cntvalue_updated_sync;
       end
       "ASYNC" , "MANUAL" : begin
         CNTVALUEOUT_out = idelay_count_async;
         cntvalue_updated = cntvalue_updated_async;
       end
       default: $display("Error: [Unisim %s-1] UPDATE_MODE_REG=%s is not valid value. Instance: %m", MODULE_NAME, UPDATE_MODE_REG);
           endcase 
    end

//----------------------------------------------------------------------
//--------------------------  DELAY_COUNT  ----------------------------
//----------------------------------------------------------------------
  always @(CLK_in or RST_in or RST_sync3 or RST_sync2 or RST_sync1)  begin
    if (RST_in == 1'b1 || RST_sync3 == 1'b1 || RST_sync2 == 1'b1 || RST_sync1 == 1'b1)
      clk_smux = 1'b0;
    else if (RST_sync3 == 1'b0)
      clk_smux = CLK_in;
  end

  always @(posedge CLK_in) begin
    RST_sync1 <= RST_in;
    RST_sync2 <= RST_sync1;
    RST_sync3 <= RST_sync2;
  end

    always @(posedge clk_smux) begin
  if (RST_in == 1'b0 && RST_sync1 == 1'b0 && RST_sync2 == 1'b0 && RST_sync3 == 1'b0) begin
  case(DELAY_TYPE_REG)
      "FIXED": ; //Do nothing.
      "VAR_LOAD":
              if (EN_VTC_in == 1'b0) begin
        casex({LOAD_in, CE_in, INC_in})
          3'b000: ; //Do nothing.
          3'b001: ; //Do nothing.
          3'b010: 
            begin //{
                                                        if (idelay_count_async >  MIN_DELAY_COUNT) begin
                idelay_count_async <= idelay_count_async-1;
                if(UPDATE_MODE_BIN != UPDATE_MODE_MANUAL)
                cntvalue_updated_async <= idelay_count_async-1;
              end  
                                                        else if (idelay_count_async == MIN_DELAY_COUNT) begin
                                                          idelay_count_async <= MAX_DELAY_COUNT;
                if(UPDATE_MODE_BIN != UPDATE_MODE_MANUAL)
                cntvalue_updated_async <= MAX_DELAY_COUNT;
                    end
            end //}
          3'b011: 
            begin //{
                                                        if (idelay_count_async < MAX_DELAY_COUNT) begin
                                                          idelay_count_async <= idelay_count_async + 1;
                if(UPDATE_MODE_BIN != UPDATE_MODE_MANUAL)
                cntvalue_updated_async <= idelay_count_async + 1;
              end  
                                                        else if (idelay_count_async == MAX_DELAY_COUNT) begin
                                                          idelay_count_async <= MIN_DELAY_COUNT;
                if(UPDATE_MODE_BIN != UPDATE_MODE_MANUAL)
                cntvalue_updated_async <= MIN_DELAY_COUNT;
                    end    
            end //}
          3'b100, 3'b101: 
            begin //{
              idelay_count_async <= CNTVALUEIN_INTEGER;
              if(UPDATE_MODE_BIN != UPDATE_MODE_MANUAL)
                cntvalue_updated_async <= CNTVALUEIN_INTEGER;
            end //}
          3'b110: 
            if(UPDATE_MODE_BIN != UPDATE_MODE_MANUAL) 
              $display("Error: [Unisim %s-2] Invalid scenario. LOAD = 1, CE = 1 INC = 0 is not valid for UPDATE_MODE=%s and DELAY_TYPE=%s. Instance: %m", MODULE_NAME, UPDATE_MODE_REG, DELAY_TYPE_REG);
            else cntvalue_updated_async <= idelay_count_async;
          3'b111: 
            if(UPDATE_MODE_BIN != UPDATE_MODE_MANUAL) 
              $display("Error: [Unisim %s-3] Invalid scenario. LOAD = 1, CE = 1 INC = 0 is not valid for UPDATE_MODE=%s and DELAY_TYPE=%s. Instance: %m", MODULE_NAME, UPDATE_MODE_REG, DELAY_TYPE_REG);
            else idelay_count_async <= idelay_count_async + CNTVALUEIN_INTEGER;
          default: $display("Error: [Unisim %s-4] Invalid scenario. LOAD = %b, CE = %b INC = %b. Instance: %m", MODULE_NAME, LOAD_in, CE_in, INC_in);
        endcase
        end
      "VARIABLE":
              if (EN_VTC_in == 1'b0) begin
        casex({LOAD_in, CE_in, INC_in})
          3'b000: ; //Do nothing.
          3'b001: ; //Do nothing.
          3'b010: 
            begin //{
                if (idelay_count_async >  MIN_DELAY_COUNT) begin 
                  idelay_count_async <= idelay_count_async-1;
                  cntvalue_updated_async <= idelay_count_async-1;
                end
                                                        else if (idelay_count_async == MIN_DELAY_COUNT) begin
                                                          idelay_count_async <= MAX_DELAY_COUNT;
                cntvalue_updated_async <= MAX_DELAY_COUNT;
              end
            end //}
          3'b011: 
            begin //{
                    if (idelay_count_async < MAX_DELAY_COUNT) begin
                                                          idelay_count_async <= idelay_count_async + 1;
                cntvalue_updated_async <= idelay_count_async + 1;
              end  
                                                        else if (idelay_count_async == MAX_DELAY_COUNT) begin
                                                          idelay_count_async <= MIN_DELAY_COUNT;
                cntvalue_updated_async <= MIN_DELAY_COUNT;
              end  
            end //}
          default: $display("Error: [Unisim %s-5] Invalid scenario. LOAD = %b, CE = %b, INC = %b, DELAY_TYPE=%s. Instance: %m", MODULE_NAME, LOAD_in, CE_in, INC_in, DELAY_TYPE_REG);
        endcase
        end
      default: $display("Error: [Unisim %s-6] DELAY_TYPE=%s is not a valid value. Instance: %m", MODULE_NAME, DELAY_TYPE_REG);
    endcase
        end
    end // always @ (posedge CLK_in)

  always @(data_mux) begin
    data_mux_sync = data_mux_sync4;
    data_mux_sync4 = data_mux_sync3;
    data_mux_sync3 = data_mux_sync2;
    data_mux_sync2 = data_mux_sync1;
    data_mux_sync1 = data_mux;
  end

  always @(data_mux_sync) begin
    cntvalue_updated_sync = cntvalue_updated_async;
  end

    always @(CNTVALUEIN_in or glblGSR) begin
      CNTVALUEIN_INTEGER = CNTVALUEIN_in;
    end   

//*********************************************************
//*** SELECT IDATA signal
//*********************************************************

    always @(DATAIN_in or IDATAIN_in or CASC_IN_in or CASC_RETURN_in or CASCADE_REG or LOOPBACK_REG) begin
      case (LOOPBACK_REG)
      "TRUE" : begin
                 data_mux = CASC_RETURN_in;
                 cdataout_pre = 1'b0;
                 end
      "FALSE": begin
         case (CASCADE_REG)
         "NONE": begin
            case (DELAY_SRC_REG)
            "IDATAIN" : begin
                        data_mux = IDATAIN_in;
                        cdataout_pre = IDATAIN_in;
                        end
            "DATAIN"  : begin
                        data_mux = DATAIN_in;
                        cdataout_pre = DATAIN_in;
                        end
            default   : begin
                        $display("Error: [Unisim %s-7] The attribute DELAY_SRC is set to %s.  Legal values for this attribute are DATAIN or IDATAIN. Instance: %m", MODULE_NAME, DELAY_SRC_REG);
                        $finish;
                        end
            endcase // case(IDELAY_SRC_reg)
         end
         "MASTER": begin
            case (DELAY_SRC_REG)
            "IDATAIN" : begin
                        data_mux = CASC_RETURN_in;
                        cdataout_pre = IDATAIN_in;
                        end
            "DATAIN"  : begin
                        data_mux = CASC_RETURN_in;
                        cdataout_pre = DATAIN_in;
                        end
            default   : begin
                        $display("Error: [Unisim %s-8] The attribute DELAY_SRC is set to %s.  Legal values for this attribute are DATAIN or IDATAIN. Instance: %m", MODULE_NAME, DELAY_SRC_REG);
                        $finish;
                        end
            endcase // case(IDELAY_SRC_reg)
            end
         "SLAVE_END" : begin
                       data_mux = CASC_IN_in;
                       cdataout_pre = 1'b0;
                       end
         "SLAVE_MIDDLE" : begin
                          data_mux = CASC_RETURN_in;
                          cdataout_pre = CASC_IN_in;
                          end
         default : begin
                   $display("Error: [Unisim %s-9] The attribute CASCADE is set to %s.  Legal values for this attribute are NONE or MASTER or SLAVE_END or SLAVE_MIDDLE. Instance: %m", MODULE_NAME, CASCADE_REG);
                   $finish;
                   end         
         endcase // case(CASCADE_REG)
         end
      default : begin
                $display("Error: [Unisim %s-10] The attribute LOOPBACK is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, LOOPBACK_REG);
                $finish;
                end
      endcase
    end // always @(DATAIN_in or IDATAIN_in or CASC_IN_in)

    always @ (cntvalue_updated or data_mux or CASC_RETURN_in or DELAY_FORMAT_REG) begin
        delay_value = (cntvalue_updated[2:0]*PER_BIT_FINE_DELAY) + (cntvalue_updated[8:3]*PER_BIT_MEDIUM_DELAY) + INTRINSIC_FINE_DELAY + INTRINSIC_MEDIUM_DELAY ;
     case (LOOPBACK_REG) 
       "TRUE" : begin
                delay_value = delay_value + CASC_RET_INTRINSIC_DELAY;
                end
       "FALSE" : begin
         case (CASCADE_REG)
           "NONE" : begin
                    case (DELAY_SRC_REG)
                      "IDATAIN" : begin
                                  delay_value = delay_value + IDATAIN_INTRINSIC_DELAY;
                                  end
                      "DATAIN"  : begin
                                  delay_value = delay_value + DATAIN_INTRINSIC_DELAY;
                                  end
                      default   : begin
                                  $display("Error: [Unisim %s-11] The attribute DELAY_SRC is set to %s.  Legal values for this attribute are DATAIN or IDATAIN. Instance: %m", MODULE_NAME, DELAY_SRC_REG);
                                  $finish;
                                  end
                      endcase // case(DELAY_SRC_reg)
                      end
           "MASTER","SLAVE_MIDDLE" : begin
                                     delay_value = delay_value + CASC_RET_INTRINSIC_DELAY;
                                     end
           "SLAVE_END" : begin
                         delay_value = delay_value + CASC_IN_INTRINSIC_DELAY;
                         end
           default     : begin
                         $display("Error: [Unisim %s-12] The attribute CASCADE is set to %s.  Legal values for this attribute are NONE or MASTER or SLAVE_END or SLAVE_MIDDLE. Instance: %m", MODULE_NAME, CASCADE_REG);
                         $finish;
                         end
           endcase // case(CASCADE_REG)
    end
    default : begin
                   $display("Error: [Unisim %s-13] The attribute LOOPBACK is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, LOOPBACK_REG);
                        $finish;
    end
  endcase
     
     
   end
 
 always @ (*) begin
   tap_out <= #delay_value data_mux;
 end

// end behavioral model

`ifdef XIL_TIMING
  wire clk_en_n;
  wire clk_en_p;
  
  assign clk_en_n =  IS_CLK_INVERTED_REG;
  assign clk_en_p = ~IS_CLK_INVERTED_REG;
`endif

  wire ci_co_en;
  wire ci_do_en;
  wire cr_do_en;
  wire d_co_en;
  wire d_do_en;
  wire id_co_en;
  wire id_do_en;

  assign ci_co_en = (delay_value == 0) && (LOOPBACK_REG == "FALSE") && (CASCADE_REG == "SLAVE_MIDDLE");
  assign ci_do_en = (delay_value == 0) && (LOOPBACK_REG == "FALSE") && (CASCADE_REG == "SLAVE_END");
  assign cr_do_en = (delay_value == 0) && (LOOPBACK_REG == "TRUE") ||
                                          (CASCADE_REG == "SLAVE_MIDDLE") || (CASCADE_REG == "MASTER");
  assign d_co_en  = (delay_value == 0) && (LOOPBACK_REG == "FALSE") &&
                                          ((CASCADE_REG == "NONE") || (CASCADE_REG == "MASTER")) &&
                                          (DELAY_SRC_REG == "DATAIN");
  assign d_do_en  = (delay_value == 0) && (LOOPBACK_REG == "FALSE") && (CASCADE_REG == "NONE") &&
                                          (DELAY_SRC_REG == "DATAIN");
  assign id_co_en = (delay_value == 0) && (LOOPBACK_REG == "FALSE") &&
                                          ((CASCADE_REG == "NONE") || (CASCADE_REG == "MASTER")) &&
                                          (DELAY_SRC_REG == "IDATAIN");
  assign id_do_en = (delay_value == 0) && (LOOPBACK_REG == "FALSE") && (CASCADE_REG == "NONE") &&
                                          (DELAY_SRC_REG == "IDATAIN");

  specify
    if (ci_co_en) (CASC_IN => CASC_OUT) = (0:0:0, 0:0:0);
    if (ci_do_en) (CASC_IN => DATAOUT) = (0:0:0, 0:0:0);
    if (cr_do_en) (CASC_RETURN => DATAOUT) = (0:0:0, 0:0:0);
    (CLK *> CNTVALUEOUT) = (100:100:100, 100:100:100);
    if (d_co_en) (DATAIN => CASC_OUT) = (0:0:0, 0:0:0);
    if (d_do_en) (DATAIN => DATAOUT) = (0:0:0, 0:0:0);
    if (id_co_en) (IDATAIN => CASC_OUT) = (0:0:0, 0:0:0);
    if (id_do_en) (IDATAIN => DATAOUT) = (0:0:0, 0:0:0);
    (negedge RST *> (CNTVALUEOUT +: 0)) = (100:100:100, 100:100:100);
    (posedge RST *> (CNTVALUEOUT +: 0)) = (100:100:100, 100:100:100);
    //if (gen_mc_fixed_dly_ratio[8:0] == 'b0) (negedge RST *> (CNTVALUEOUT +: 0)) = (100:100:100, 100:100:100);
    //if (gen_mc_fixed_dly_ratio[8:0] != 'b0) (negedge RST *> (CNTVALUEOUT +: 1)) = (100:100:100, 100:100:100);
    //if (gen_mc_fixed_dly_ratio[8:0] == 'b0) (posedge RST *> (CNTVALUEOUT +: 0)) = (100:100:100, 100:100:100);
    //if (gen_mc_fixed_dly_ratio[8:0] != 'b0) (posedge RST *> (CNTVALUEOUT +: 1)) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $period (negedge CLK, 0:0:0, notifier);
    $period (posedge CLK, 0:0:0, notifier);
    $setuphold (negedge CLK, negedge CE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CE_delay);
    $setuphold (negedge CLK, negedge CNTVALUEIN, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay);
    $setuphold (negedge CLK, negedge INC, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, INC_delay);
    $setuphold (negedge CLK, negedge LOAD, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, LOAD_delay);
    $setuphold (negedge CLK, posedge CE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CE_delay);
    $setuphold (negedge CLK, posedge CNTVALUEIN, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CNTVALUEIN_delay);
    $setuphold (negedge CLK, posedge INC, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, INC_delay);
    $setuphold (negedge CLK, posedge LOAD, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, LOAD_delay);
    $setuphold (posedge CLK, negedge CE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CE_delay);
    $setuphold (posedge CLK, negedge CNTVALUEIN, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay);
    $setuphold (posedge CLK, negedge INC, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, INC_delay);
    $setuphold (posedge CLK, negedge LOAD, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, LOAD_delay);
    $setuphold (posedge CLK, posedge CE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CE_delay);
    $setuphold (posedge CLK, posedge CNTVALUEIN, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CNTVALUEIN_delay);
    $setuphold (posedge CLK, posedge INC, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, INC_delay);
    $setuphold (posedge CLK, posedge LOAD, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, LOAD_delay);
    $width (negedge CLK, 0:0:0, 0, notifier);
    $width (negedge RST, 0:0:0, 0, notifier);
    $width (posedge CLK, 0:0:0, 0, notifier);
    $width (posedge RST, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
