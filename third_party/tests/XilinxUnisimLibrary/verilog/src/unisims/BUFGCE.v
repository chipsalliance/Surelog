///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2018 Xilinx, Inc.
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
// \   \   \/      Version     : 2019.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        General Clock Buffer with Clock Enable
// /___/   /\      Filename    : BUFGCE.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//    05/15/12 - Initial version.
//    10/22/14 - 808642 - Added #1 to $finish
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module BUFGCE #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter CE_TYPE = "SYNC",
  parameter [0:0] IS_CE_INVERTED = 1'b0,
  parameter [0:0] IS_I_INVERTED = 1'b0,
  parameter SIM_DEVICE = "ULTRASCALE",
  parameter STARTUP_SYNC = "FALSE"
)(
  output O,

  input CE,
  input I
);
  
// define constants
  localparam MODULE_NAME = "BUFGCE";

// Parameter encodings and registers
  localparam CE_TYPE_ASYNC = 1;
  localparam CE_TYPE_HARDSYNC = 2;
  localparam CE_TYPE_SYNC = 0;
  localparam SIM_DEVICE_7SERIES = 1;
  localparam SIM_DEVICE_ULTRASCALE = 0;
  localparam SIM_DEVICE_ULTRASCALE_PLUS = 2;
  localparam SIM_DEVICE_VERSAL_AI_CORE = 4;
  localparam SIM_DEVICE_VERSAL_AI_CORE_ES1 = 5;
  localparam SIM_DEVICE_VERSAL_AI_CORE_ES2 = 6;
  localparam SIM_DEVICE_VERSAL_AI_EDGE = 7;
  localparam SIM_DEVICE_VERSAL_AI_EDGE_ES1 = 8;
  localparam SIM_DEVICE_VERSAL_AI_EDGE_ES2 = 9;
  localparam SIM_DEVICE_VERSAL_AI_RF = 10;
  localparam SIM_DEVICE_VERSAL_AI_RF_ES1 = 11;
  localparam SIM_DEVICE_VERSAL_AI_RF_ES2 = 12;
  localparam SIM_DEVICE_VERSAL_HBM = 15;
  localparam SIM_DEVICE_VERSAL_HBM_ES1 = 16;
  localparam SIM_DEVICE_VERSAL_HBM_ES2 = 17;
  localparam SIM_DEVICE_VERSAL_PREMIUM = 18;
  localparam SIM_DEVICE_VERSAL_PREMIUM_ES1 = 19;
  localparam SIM_DEVICE_VERSAL_PREMIUM_ES2 = 20;
  localparam SIM_DEVICE_VERSAL_PRIME = 21;
  localparam SIM_DEVICE_VERSAL_PRIME_ES1 = 22;
  localparam SIM_DEVICE_VERSAL_PRIME_ES2 = 23;
  localparam STARTUP_SYNC_FALSE = 0;
  localparam STARTUP_SYNC_TRUE = 1;

  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "BUFGCE_dr.v"
`else
  reg [64:1] CE_TYPE_REG = CE_TYPE;
  reg [0:0] IS_CE_INVERTED_REG = IS_CE_INVERTED;
  reg [0:0] IS_I_INVERTED_REG = IS_I_INVERTED;
  reg [144:1] SIM_DEVICE_REG = SIM_DEVICE;
  reg [40:1] STARTUP_SYNC_REG = STARTUP_SYNC;
`endif

`ifdef XIL_XECLIB
  wire [1:0] CE_TYPE_BIN;
  wire [4:0] SIM_DEVICE_BIN;
  wire STARTUP_SYNC_BIN;
`else
  reg [1:0] CE_TYPE_BIN;
  reg [4:0] SIM_DEVICE_BIN;
  reg STARTUP_SYNC_BIN;
`endif

`ifdef XIL_XECLIB
reg glblGSR = 1'b0;
`else
tri0 glblGSR = glbl.GSR;
`endif

  wire CE_in;
  wire I_in;

`ifdef XIL_TIMING
  wire CE_delay;
  wire I_delay;
`endif

`ifdef XIL_TIMING
  assign CE_in = (CE === 1'bz) || (CE_delay ^ IS_CE_INVERTED_REG); // rv 1
  assign I_in = I_delay ^ IS_I_INVERTED_REG;
`else
  assign CE_in = (CE === 1'bz) || (CE ^ IS_CE_INVERTED_REG); // rv 1
  assign I_in = I ^ IS_I_INVERTED_REG;
`endif

`ifndef XIL_XECLIB
  reg attr_test;
  reg attr_err;
  
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

`ifdef XIL_XECLIB
  assign CE_TYPE_BIN =
    (CE_TYPE_REG == "SYNC") ? CE_TYPE_SYNC :
    (CE_TYPE_REG == "ASYNC") ? CE_TYPE_ASYNC :
      (CE_TYPE_REG == "HARDSYNC") ? CE_TYPE_HARDSYNC :
     CE_TYPE_SYNC;

  assign SIM_DEVICE_BIN =
      (SIM_DEVICE_REG == "ULTRASCALE") ? SIM_DEVICE_ULTRASCALE :
      (SIM_DEVICE_REG == "7SERIES") ? SIM_DEVICE_7SERIES :
      (SIM_DEVICE_REG == "ULTRASCALE_PLUS") ? SIM_DEVICE_ULTRASCALE_PLUS :
      (SIM_DEVICE_REG == "VERSAL_AI_CORE") ? SIM_DEVICE_VERSAL_AI_CORE :
      (SIM_DEVICE_REG == "VERSAL_AI_CORE_ES1") ? SIM_DEVICE_VERSAL_AI_CORE_ES1 :
      (SIM_DEVICE_REG == "VERSAL_AI_CORE_ES2") ? SIM_DEVICE_VERSAL_AI_CORE_ES2 :
      (SIM_DEVICE_REG == "VERSAL_AI_EDGE") ? SIM_DEVICE_VERSAL_AI_EDGE :
      (SIM_DEVICE_REG == "VERSAL_AI_EDGE_ES1") ? SIM_DEVICE_VERSAL_AI_EDGE_ES1 :
      (SIM_DEVICE_REG == "VERSAL_AI_EDGE_ES2") ? SIM_DEVICE_VERSAL_AI_EDGE_ES2 :
      (SIM_DEVICE_REG == "VERSAL_AI_RF") ? SIM_DEVICE_VERSAL_AI_RF :
      (SIM_DEVICE_REG == "VERSAL_AI_RF_ES1") ? SIM_DEVICE_VERSAL_AI_RF_ES1 :
      (SIM_DEVICE_REG == "VERSAL_AI_RF_ES2") ? SIM_DEVICE_VERSAL_AI_RF_ES2 :
      (SIM_DEVICE_REG == "VERSAL_HBM") ? SIM_DEVICE_VERSAL_HBM :
      (SIM_DEVICE_REG == "VERSAL_HBM_ES1") ? SIM_DEVICE_VERSAL_HBM_ES1 :
      (SIM_DEVICE_REG == "VERSAL_HBM_ES2") ? SIM_DEVICE_VERSAL_HBM_ES2 :
      (SIM_DEVICE_REG == "VERSAL_PREMIUM") ? SIM_DEVICE_VERSAL_PREMIUM :
      (SIM_DEVICE_REG == "VERSAL_PREMIUM_ES1") ? SIM_DEVICE_VERSAL_PREMIUM_ES1 :
      (SIM_DEVICE_REG == "VERSAL_PREMIUM_ES2") ? SIM_DEVICE_VERSAL_PREMIUM_ES2 :
      (SIM_DEVICE_REG == "VERSAL_PRIME") ? SIM_DEVICE_VERSAL_PRIME :
      (SIM_DEVICE_REG == "VERSAL_PRIME_ES1") ? SIM_DEVICE_VERSAL_PRIME_ES1 :
      (SIM_DEVICE_REG == "VERSAL_PRIME_ES2") ? SIM_DEVICE_VERSAL_PRIME_ES2 :
       SIM_DEVICE_ULTRASCALE;
  
  assign STARTUP_SYNC_BIN =
      (STARTUP_SYNC_REG == "FALSE") ? STARTUP_SYNC_FALSE :
      (STARTUP_SYNC_REG == "TRUE") ? STARTUP_SYNC_TRUE :
       STARTUP_SYNC_FALSE;
  
`else
  always @ (trig_attr) begin
    #1;
    CE_TYPE_BIN =
      (CE_TYPE_REG == "SYNC") ? CE_TYPE_SYNC :
      (CE_TYPE_REG == "ASYNC") ? CE_TYPE_ASYNC :
      (CE_TYPE_REG == "HARDSYNC") ? CE_TYPE_HARDSYNC :
       CE_TYPE_SYNC;

  SIM_DEVICE_BIN =
      (SIM_DEVICE_REG == "ULTRASCALE") ? SIM_DEVICE_ULTRASCALE :
      (SIM_DEVICE_REG == "7SERIES") ? SIM_DEVICE_7SERIES :
      (SIM_DEVICE_REG == "ULTRASCALE_PLUS") ? SIM_DEVICE_ULTRASCALE_PLUS :
      (SIM_DEVICE_REG == "VERSAL_AI_CORE") ? SIM_DEVICE_VERSAL_AI_CORE :
      (SIM_DEVICE_REG == "VERSAL_AI_CORE_ES1") ? SIM_DEVICE_VERSAL_AI_CORE_ES1 :
      (SIM_DEVICE_REG == "VERSAL_AI_CORE_ES2") ? SIM_DEVICE_VERSAL_AI_CORE_ES2 :
      (SIM_DEVICE_REG == "VERSAL_AI_EDGE") ? SIM_DEVICE_VERSAL_AI_EDGE :
      (SIM_DEVICE_REG == "VERSAL_AI_EDGE_ES1") ? SIM_DEVICE_VERSAL_AI_EDGE_ES1 :
      (SIM_DEVICE_REG == "VERSAL_AI_EDGE_ES2") ? SIM_DEVICE_VERSAL_AI_EDGE_ES2 :
      (SIM_DEVICE_REG == "VERSAL_AI_RF") ? SIM_DEVICE_VERSAL_AI_RF :
      (SIM_DEVICE_REG == "VERSAL_AI_RF_ES1") ? SIM_DEVICE_VERSAL_AI_RF_ES1 :
      (SIM_DEVICE_REG == "VERSAL_AI_RF_ES2") ? SIM_DEVICE_VERSAL_AI_RF_ES2 :
      (SIM_DEVICE_REG == "VERSAL_HBM") ? SIM_DEVICE_VERSAL_HBM :
      (SIM_DEVICE_REG == "VERSAL_HBM_ES1") ? SIM_DEVICE_VERSAL_HBM_ES1 :
      (SIM_DEVICE_REG == "VERSAL_HBM_ES2") ? SIM_DEVICE_VERSAL_HBM_ES2 :
      (SIM_DEVICE_REG == "VERSAL_PREMIUM") ? SIM_DEVICE_VERSAL_PREMIUM :
      (SIM_DEVICE_REG == "VERSAL_PREMIUM_ES1") ? SIM_DEVICE_VERSAL_PREMIUM_ES1 :
      (SIM_DEVICE_REG == "VERSAL_PREMIUM_ES2") ? SIM_DEVICE_VERSAL_PREMIUM_ES2 :
      (SIM_DEVICE_REG == "VERSAL_PRIME") ? SIM_DEVICE_VERSAL_PRIME :
      (SIM_DEVICE_REG == "VERSAL_PRIME_ES1") ? SIM_DEVICE_VERSAL_PRIME_ES1 :
      (SIM_DEVICE_REG == "VERSAL_PRIME_ES2") ? SIM_DEVICE_VERSAL_PRIME_ES2 :
       SIM_DEVICE_ULTRASCALE;
  
  STARTUP_SYNC_BIN =
      (STARTUP_SYNC_REG == "FALSE") ? STARTUP_SYNC_FALSE :
      (STARTUP_SYNC_REG == "TRUE") ? STARTUP_SYNC_TRUE :
       STARTUP_SYNC_FALSE;
  
  end
`endif

`ifndef XIL_XECLIB
  always @ (trig_attr) begin
  #1;
    if ((attr_test == 1'b1) ||
        ((CE_TYPE_REG != "SYNC") &&
         (CE_TYPE_REG != "ASYNC") &&
         (CE_TYPE_REG != "HARDSYNC"))) begin
      $display("Error: [Unisim %s-101] CE_TYPE attribute is set to %s.  Legal values for this attribute are SYNC, ASYNC or HARDSYNC. Instance: %m", MODULE_NAME, CE_TYPE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE") &&
         (SIM_DEVICE_REG != "7SERIES") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE_REG != "VERSAL_AI_CORE") &&
         (SIM_DEVICE_REG != "VERSAL_AI_CORE_ES1") &&
         (SIM_DEVICE_REG != "VERSAL_AI_CORE_ES2") &&
         (SIM_DEVICE_REG != "VERSAL_AI_EDGE") &&
         (SIM_DEVICE_REG != "VERSAL_AI_EDGE_ES1") &&
         (SIM_DEVICE_REG != "VERSAL_AI_EDGE_ES2") &&
         (SIM_DEVICE_REG != "VERSAL_AI_RF") &&
         (SIM_DEVICE_REG != "VERSAL_AI_RF_ES1") &&
         (SIM_DEVICE_REG != "VERSAL_AI_RF_ES2") &&
         (SIM_DEVICE_REG != "VERSAL_HBM") &&
         (SIM_DEVICE_REG != "VERSAL_HBM_ES1") &&
         (SIM_DEVICE_REG != "VERSAL_HBM_ES2") &&
         (SIM_DEVICE_REG != "VERSAL_PREMIUM") &&
         (SIM_DEVICE_REG != "VERSAL_PREMIUM_ES1") &&
         (SIM_DEVICE_REG != "VERSAL_PREMIUM_ES2") &&
         (SIM_DEVICE_REG != "VERSAL_PRIME") &&
         (SIM_DEVICE_REG != "VERSAL_PRIME_ES1") &&
         (SIM_DEVICE_REG != "VERSAL_PRIME_ES2"))) begin
      $display("Error: [Unisim %s-104] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE, 7SERIES, ULTRASCALE_PLUS, VERSAL_AI_CORE, VERSAL_AI_CORE_ES1, VERSAL_AI_CORE_ES2, VERSAL_AI_EDGE, VERSAL_AI_EDGE_ES1, VERSAL_AI_EDGE_ES2, VERSAL_AI_RF, VERSAL_AI_RF_ES1, VERSAL_AI_RF_ES2, VERSAL_HBM, VERSAL_HBM_ES1, VERSAL_HBM_ES2, VERSAL_PREMIUM, VERSAL_PREMIUM_ES1, VERSAL_PREMIUM_ES2, VERSAL_PRIME, VERSAL_PRIME_ES1 or VERSAL_PRIME_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((STARTUP_SYNC_REG != "FALSE") &&
         (STARTUP_SYNC_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-105] STARTUP_SYNC attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, STARTUP_SYNC_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end
`endif

`ifdef XIL_TIMING
  reg notifier;
`endif

// begin behavioral model


  reg       O_out;
  reg       enable_clk;
  reg [2:0] gwe_sync;
  wire      gwe_muxed_sync;
  reg [2:0] ce_sync;
  wire      ce_muxed_sync;
  wire      cb;


  initial begin
    gwe_sync   = 3'b000;
    ce_sync    = 3'b000;
    enable_clk = 1'b0;
  end

  always @(posedge I_in ) begin
    if(I_in==1'b1)
      gwe_sync <= {gwe_sync[1:0], ~glblGSR};
  end

  assign gwe_muxed_sync = (STARTUP_SYNC_BIN == STARTUP_SYNC_TRUE) ? gwe_sync[2] :  ~glblGSR;


  always @(posedge I_in ) begin
    if(I_in==1'b1)
      ce_sync <= {ce_sync[1:0], CE_in};
  end

  assign ce_muxed_sync = (CE_TYPE_BIN == CE_TYPE_HARDSYNC) ? ce_sync[2] : CE_in;
 
  assign cb = ~( (~gwe_muxed_sync) || ((CE_TYPE_BIN !== CE_TYPE_ASYNC) && I_in));

  
  always @(*) begin
    if(cb)
      enable_clk <= ce_muxed_sync;
  end

  always @(*)
    O_out = enable_clk && I_in;

  assign O = O_out;
  
// end behavioral model

`ifndef XIL_XECLIB
`ifdef XIL_TIMING

  wire i_en_n;
  wire i_en_p;

  assign i_en_n = IS_I_INVERTED_REG;
  assign i_en_p = ~IS_I_INVERTED_REG;

`endif

`ifdef XIL_TIMING
  specify
    (CE => O) = (0:0:0, 0:0:0);
    (I => O) = (0:0:0, 0:0:0);
    $period (negedge I, 0:0:0, notifier);
    $period (posedge I, 0:0:0, notifier);
    $setuphold (negedge I, negedge CE, 0:0:0, 0:0:0, notifier, i_en_n, i_en_n, I_delay, CE_delay);
    $setuphold (negedge I, posedge CE, 0:0:0, 0:0:0, notifier, i_en_n, i_en_n, I_delay, CE_delay);
    $setuphold (posedge I, negedge CE, 0:0:0, 0:0:0, notifier, i_en_p, i_en_p, I_delay, CE_delay);
    $setuphold (posedge I, posedge CE, 0:0:0, 0:0:0, notifier, i_en_p, i_en_p, I_delay, CE_delay);
    $width (negedge CE, 0:0:0, 0, notifier);
    $width (negedge I, 0:0:0, 0, notifier);
    $width (posedge CE, 0:0:0, 0, notifier);
    $width (posedge I, 0:0:0, 0, notifier);
    specparam PATHPULSE$ = 0;
  endspecify
`endif
`endif
endmodule

`endcelldefine
