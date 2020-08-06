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
// \   \   \/      Version     : 2020.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        BUFGCE_DIV
// /___/   /\      Filename    : BUFGCE_DIV.v
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

module BUFGCE_DIV #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter integer BUFGCE_DIVIDE = 1,
  parameter CE_TYPE = "SYNC",
  parameter HARDSYNC_CLR = "FALSE",
  parameter [0:0] IS_CE_INVERTED = 1'b0,
  parameter [0:0] IS_CLR_INVERTED = 1'b0,
  parameter [0:0] IS_I_INVERTED = 1'b0,
  parameter SIM_DEVICE = "ULTRASCALE",
  parameter STARTUP_SYNC = "FALSE"
)(
  output O,

  input CE,
  input CLR,
  input I
);
  
// define constants
  localparam MODULE_NAME = "BUFGCE_DIV";

// Parameter encodings and registers
  localparam CE_TYPE_HARDSYNC = 1;
  localparam CE_TYPE_SYNC = 0;
  localparam HARDSYNC_CLR_FALSE = 0;
  localparam HARDSYNC_CLR_TRUE = 1;
  localparam SIM_DEVICE_ULTRASCALE = 0;
  localparam SIM_DEVICE_ULTRASCALE_PLUS = 1;
  localparam SIM_DEVICE_VERSAL_AI_CORE = 3;
  localparam SIM_DEVICE_VERSAL_AI_CORE_ES1 = 4;
  localparam SIM_DEVICE_VERSAL_AI_CORE_ES2 = 5;
  localparam SIM_DEVICE_VERSAL_AI_EDGE = 6;
  localparam SIM_DEVICE_VERSAL_AI_EDGE_ES1 = 7;
  localparam SIM_DEVICE_VERSAL_AI_EDGE_ES2 = 8;
  localparam SIM_DEVICE_VERSAL_AI_RF = 9;
  localparam SIM_DEVICE_VERSAL_AI_RF_ES1 = 10;
  localparam SIM_DEVICE_VERSAL_AI_RF_ES2 = 11;
  localparam SIM_DEVICE_VERSAL_HBM = 14;
  localparam SIM_DEVICE_VERSAL_HBM_ES1 = 15;
  localparam SIM_DEVICE_VERSAL_HBM_ES2 = 16;
  localparam SIM_DEVICE_VERSAL_PREMIUM = 17;
  localparam SIM_DEVICE_VERSAL_PREMIUM_ES1 = 18;
  localparam SIM_DEVICE_VERSAL_PREMIUM_ES2 = 19;
  localparam SIM_DEVICE_VERSAL_PRIME = 20;
  localparam SIM_DEVICE_VERSAL_PRIME_ES1 = 21;
  localparam SIM_DEVICE_VERSAL_PRIME_ES2 = 22;
  localparam STARTUP_SYNC_FALSE = 0;
  localparam STARTUP_SYNC_TRUE = 1;

  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "BUFGCE_DIV_dr.v"
`else
  reg [31:0] BUFGCE_DIVIDE_REG = BUFGCE_DIVIDE;
  reg [64:1] CE_TYPE_REG = CE_TYPE;
  reg [40:1] HARDSYNC_CLR_REG = HARDSYNC_CLR;
  reg [0:0] IS_CE_INVERTED_REG = IS_CE_INVERTED;
  reg [0:0] IS_CLR_INVERTED_REG = IS_CLR_INVERTED;
  reg [0:0] IS_I_INVERTED_REG = IS_I_INVERTED;
  reg [144:1] SIM_DEVICE_REG = SIM_DEVICE;
  reg [40:1] STARTUP_SYNC_REG = STARTUP_SYNC;
`endif

`ifdef XIL_XECLIB
  wire [3:0] BUFGCE_DIVIDE_BIN;
  wire CE_TYPE_BIN;
  wire HARDSYNC_CLR_BIN;
  wire [4:0] SIM_DEVICE_BIN;
  wire STARTUP_SYNC_BIN;
`else
  reg [3:0] BUFGCE_DIVIDE_BIN;
  reg CE_TYPE_BIN;
  reg HARDSYNC_CLR_BIN;
  reg [4:0] SIM_DEVICE_BIN;
  reg STARTUP_SYNC_BIN;
`endif

`ifdef XIL_XECLIB
  reg glblGSR = 1'b0;
`else
  tri0 glblGSR = glbl.GSR;
`endif

  wire CE_in;
  wire CLR_in;
  wire I_in;

`ifdef XIL_TIMING
  wire CE_delay;
  wire CLR_delay;
  wire I_delay;
`endif

`ifdef XIL_TIMING
  assign CE_in = (CE === 1'bz) || (CE_delay ^ IS_CE_INVERTED_REG); // rv 1
  assign CLR_in = (CLR !== 1'bz) && (CLR_delay ^ IS_CLR_INVERTED_REG); // rv 0
  assign I_in = I_delay ^ IS_I_INVERTED_REG;
`else
  assign CE_in = (CE === 1'bz) || (CE ^ IS_CE_INVERTED_REG); // rv 1
  assign CLR_in = (CLR !== 1'bz) && (CLR ^ IS_CLR_INVERTED_REG); // rv 0
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
  assign BUFGCE_DIVIDE_BIN = BUFGCE_DIVIDE_REG[3:0];
  
  assign CE_TYPE_BIN =
      (CE_TYPE_REG == "SYNC") ? CE_TYPE_SYNC :
      (CE_TYPE_REG == "HARDSYNC") ? CE_TYPE_HARDSYNC :
       CE_TYPE_SYNC;
  
  assign HARDSYNC_CLR_BIN =
      (HARDSYNC_CLR_REG == "FALSE") ? HARDSYNC_CLR_FALSE :
      (HARDSYNC_CLR_REG == "TRUE") ? HARDSYNC_CLR_TRUE :
       HARDSYNC_CLR_FALSE;
  
  assign SIM_DEVICE_BIN =
      (SIM_DEVICE_REG == "ULTRASCALE") ? SIM_DEVICE_ULTRASCALE :
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
  BUFGCE_DIVIDE_BIN = BUFGCE_DIVIDE_REG[3:0];
  
  CE_TYPE_BIN =
      (CE_TYPE_REG == "SYNC") ? CE_TYPE_SYNC :
      (CE_TYPE_REG == "HARDSYNC") ? CE_TYPE_HARDSYNC :
       CE_TYPE_SYNC;
  
  HARDSYNC_CLR_BIN =
      (HARDSYNC_CLR_REG == "FALSE") ? HARDSYNC_CLR_FALSE :
      (HARDSYNC_CLR_REG == "TRUE") ? HARDSYNC_CLR_TRUE :
       HARDSYNC_CLR_FALSE;
  
  SIM_DEVICE_BIN =
      (SIM_DEVICE_REG == "ULTRASCALE") ? SIM_DEVICE_ULTRASCALE :
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
        ((BUFGCE_DIVIDE_REG != 1) &&
         (BUFGCE_DIVIDE_REG != 2) &&
         (BUFGCE_DIVIDE_REG != 3) &&
         (BUFGCE_DIVIDE_REG != 4) &&
         (BUFGCE_DIVIDE_REG != 5) &&
         (BUFGCE_DIVIDE_REG != 6) &&
         (BUFGCE_DIVIDE_REG != 7) &&
         (BUFGCE_DIVIDE_REG != 8))) begin
      $display("Error: [Unisim %s-101] BUFGCE_DIVIDE attribute is set to %d.  Legal values for this attribute are 1, 2, 3, 4, 5, 6, 7 or 8. Instance: %m", MODULE_NAME, BUFGCE_DIVIDE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CE_TYPE_REG != "SYNC") &&
         (CE_TYPE_REG != "HARDSYNC"))) begin
      $display("Error: [Unisim %s-102] CE_TYPE attribute is set to %s.  Legal values for this attribute are SYNC or HARDSYNC. Instance: %m", MODULE_NAME, CE_TYPE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((HARDSYNC_CLR_REG != "FALSE") &&
         (HARDSYNC_CLR_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-103] HARDSYNC_CLR attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, HARDSYNC_CLR_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE") &&
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
      $display("Error: [Unisim %s-107] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE, ULTRASCALE_PLUS, VERSAL_AI_CORE, VERSAL_AI_CORE_ES1, VERSAL_AI_CORE_ES2, VERSAL_AI_EDGE, VERSAL_AI_EDGE_ES1, VERSAL_AI_EDGE_ES2, VERSAL_AI_RF, VERSAL_AI_RF_ES1, VERSAL_AI_RF_ES2, VERSAL_HBM, VERSAL_HBM_ES1, VERSAL_HBM_ES2, VERSAL_PREMIUM, VERSAL_PREMIUM_ES1, VERSAL_PREMIUM_ES2, VERSAL_PRIME, VERSAL_PRIME_ES1 or VERSAL_PRIME_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((STARTUP_SYNC_REG != "FALSE") &&
         (STARTUP_SYNC_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-108] STARTUP_SYNC attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, STARTUP_SYNC_REG);
      attr_err = 1'b1;
    end
    
  if (attr_err == 1'b1) #1 $finish;
  end
`endif

`ifdef XIL_TIMING
  reg notifier;
`endif

// begin behavioral model

  integer       clk_count, first_toggle_count, second_toggle_count;
  reg           first_rise, first_half_period;
  reg           O_bufgce_div;
  wire          i_ce;
  wire          CLR_int;
  reg           ce_en;
  wire          gsr_muxed_sync;
  wire          ce_muxed_sync;
  wire          clr_muxed_sync;
  wire          clr_muxed_xrm;
  reg [2:0]     gwe_sync;
  reg [2:0]     ce_sync;
  reg [2:0]     clr_sync;

  always @ (trig_attr) begin
    #1;
    if (((SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF        ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF_ES1    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF_ES2    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM          ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM_ES1      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM_ES2      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME        ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME_ES1    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME_ES2    )) &&
        (STARTUP_SYNC_BIN == STARTUP_SYNC_TRUE)) begin
      $display("Warning: [Unisim %s-200] SIM_DEVICE attribute is set to %s and STARTUP_SYNC is set to %s. STARTUP_SYNC functionality is not supported for this DEVICE. Instance: %m", MODULE_NAME, SIM_DEVICE_REG, STARTUP_SYNC_REG);
      STARTUP_SYNC_BIN = STARTUP_SYNC_FALSE; //force correct
    end

    if (((SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF        ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF_ES1    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF_ES2    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM          ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM_ES1      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM_ES2      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME        ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME_ES1    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME_ES2    )) &&
        (CE_TYPE_BIN == CE_TYPE_HARDSYNC)) begin
      $display("Warning: [Unisim %s-201] SIM_DEVICE attribute is set to %s and CE_TYPE is set to %s. HARDSYNC CE functionality is not supported for this DEVICE. Instance: %m", MODULE_NAME, SIM_DEVICE_REG, CE_TYPE_REG);
      CE_TYPE_BIN = CE_TYPE_SYNC;  //force correct
    end

    if (((SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_CORE_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_EDGE_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF        ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF_ES1    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_AI_RF_ES2    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM          ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM_ES1      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_HBM_ES2      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM      ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM_ES1  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PREMIUM_ES2  ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME        ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME_ES1    ) &&
         (SIM_DEVICE_BIN != SIM_DEVICE_VERSAL_PRIME_ES2    )) &&
        (HARDSYNC_CLR == HARDSYNC_CLR_TRUE )) begin
      $display("Warning: [Unisim %s-202] SIM_DEVICE attribute is set to %s and HARDSYNC_CLR is set to %s. HARDSYNC CLR functionality is not supported for this DEVICE. Instance: %m", MODULE_NAME, SIM_DEVICE_REG, HARDSYNC_CLR_REG);
      HARDSYNC_CLR_BIN = HARDSYNC_CLR_FALSE; //force correct
    end

  end //always


  
  initial begin
    clk_count               = 1;
    first_toggle_count      = 1;
    second_toggle_count     = 1;
    O_bufgce_div            = 1'b0;
    ce_en                   = 1'b0;
    gwe_sync                = 3'b000;
    ce_sync                 = 3'b000;
    clr_sync                = 3'b111;


  end

  always @(posedge I_in) begin
    if(I_in==1'b1)
      gwe_sync <= {gwe_sync[1:0], ~glblGSR};
  end

  assign gsr_muxed_sync =  (STARTUP_SYNC_BIN == STARTUP_SYNC_TRUE) ? ~gwe_sync[2] :  glblGSR;

  always @(negedge I_in) begin
    if(I_in==1'b0)
      clr_sync <= {clr_sync[1:0], CLR_in};
  end

  assign clr_muxed_sync = (HARDSYNC_CLR_BIN == HARDSYNC_CLR_TRUE) ? clr_sync[2] : CLR_in;
  assign clr_muxed_xrm = (clr_muxed_sync ===1'bX) ? 1'b1 : clr_muxed_sync;

  always @(posedge I_in) begin
    if(I_in==1'b1)
      ce_sync <= {ce_sync[1:0], CE_in};
  end

  assign ce_muxed_sync = (CE_TYPE_BIN == CE_TYPE_HARDSYNC) ? ce_sync[2] : CE_in;
 

  always @ (trig_attr) begin
    #1;
    case (BUFGCE_DIVIDE_BIN)
      1 : begin
       first_toggle_count = 1;
       second_toggle_count = 1;
     end
      2 : begin
       first_toggle_count = 2;
       second_toggle_count = 2;
          end
      3 : begin
       first_toggle_count = 2;
       second_toggle_count = 4;
     end
      4 : begin
       first_toggle_count = 4;
       second_toggle_count = 4;
     end
      5 : begin
       first_toggle_count = 4;
       second_toggle_count = 6;
     end
      6 : begin
       first_toggle_count = 6;
       second_toggle_count = 6;
     end
      7 : begin
       first_toggle_count = 6;
       second_toggle_count = 8;
     end
      8 : begin
       first_toggle_count = 8;
       second_toggle_count = 8;
          end
    endcase // case(BUFGCE_DIV)

  end

  always begin
    if (gsr_muxed_sync == 1'b1) begin
      assign O_bufgce_div = 1'b0;
      assign clk_count = 0;
      assign first_rise = 1'b1;
      assign first_half_period = 1'b0;
    end
    else if (gsr_muxed_sync == 1'b0) begin
      deassign O_bufgce_div;
      deassign clk_count;
      deassign first_rise;
      deassign first_half_period;
    end
    @(gsr_muxed_sync);
  end

  always @(I_in, gsr_muxed_sync, ce_muxed_sync, clr_muxed_xrm) begin
    if (gsr_muxed_sync || clr_muxed_xrm)
      ce_en <= 1'b0;
    else if (~I_in)
      ce_en <= ce_muxed_sync;
  end

  assign i_ce = I_in & ce_en;

  always @(i_ce or posedge gsr_muxed_sync or posedge clr_muxed_xrm) begin
    if (first_toggle_count == 1) begin
        O_bufgce_div = i_ce;
    end
    else begin
      if(clr_muxed_xrm == 1'b1 || gsr_muxed_sync == 1'b1) begin
        O_bufgce_div = 1'b0;
        clk_count = 1;
        first_half_period = 1'b1;
        first_rise = 1'b1;
      end
      else if(clr_muxed_xrm == 1'b0 && gsr_muxed_sync == 1'b0) begin
        if (i_ce == 1'b1 && first_rise == 1'b1) begin
          O_bufgce_div = 1'b1;
          clk_count = 1;
          first_half_period = 1'b1;
          first_rise = 1'b0;
        end
        else if (clk_count == second_toggle_count && first_half_period == 1'b0) begin
          O_bufgce_div = ~O_bufgce_div;
          clk_count = 1;
          first_half_period = 1'b1;
        end
        else if (clk_count == first_toggle_count && first_half_period == 1'b1) begin
          O_bufgce_div = ~O_bufgce_div;
          clk_count = 1;
          first_half_period = 1'b0;
        end
        else if (first_rise == 1'b0) begin
          clk_count = clk_count + 1;
        end
      end
    end
  end

  assign O = O_bufgce_div;
  
// end behavioral model

`ifndef XIL_XECLIB
`ifdef XIL_TIMING

  wire i_en_n;
  wire i_en_p;

  assign i_en_n =  IS_I_INVERTED_REG;
  assign i_en_p = ~IS_I_INVERTED_REG;

`endif

  specify
    (I => O) = (0:0:0, 0:0:0);
    (negedge CLR => (O +: 0)) = (0:0:0, 0:0:0);
    (posedge CLR => (O +: 0)) = (0:0:0, 0:0:0);
`ifdef XIL_TIMING
    $period (negedge I, 0:0:0, notifier);
    $period (posedge I, 0:0:0, notifier);
    $recrem (negedge CLR, negedge I, 0:0:0, 0:0:0, notifier, i_en_n, i_en_n, CLR_delay, I_delay);
    $recrem (negedge CLR, posedge I, 0:0:0, 0:0:0, notifier, i_en_p, i_en_p, CLR_delay, I_delay);
    $recrem (posedge CLR, negedge I, 0:0:0, 0:0:0, notifier, i_en_n, i_en_n, CLR_delay, I_delay);
    $recrem (posedge CLR, posedge I, 0:0:0, 0:0:0, notifier, i_en_p, i_en_p, CLR_delay, I_delay);
    $setuphold (negedge I, negedge CE, 0:0:0, 0:0:0, notifier, i_en_n, i_en_n, I_delay, CE_delay);
    $setuphold (negedge I, negedge CLR, 0:0:0, 0:0:0, notifier, i_en_n, i_en_n, I_delay, CLR_delay);
    $setuphold (negedge I, posedge CE, 0:0:0, 0:0:0, notifier, i_en_n, i_en_n, I_delay, CE_delay);
    $setuphold (negedge I, posedge CLR, 0:0:0, 0:0:0, notifier, i_en_n, i_en_n, I_delay, CLR_delay);
    $setuphold (posedge I, negedge CE, 0:0:0, 0:0:0, notifier, i_en_p, i_en_p, I_delay, CE_delay);
    $setuphold (posedge I, negedge CLR, 0:0:0, 0:0:0, notifier, i_en_p, i_en_p, I_delay, CLR_delay);
    $setuphold (posedge I, posedge CE, 0:0:0, 0:0:0, notifier, i_en_p, i_en_p, I_delay, CE_delay);
    $setuphold (posedge I, posedge CLR, 0:0:0, 0:0:0, notifier, i_en_p, i_en_p, I_delay, CLR_delay);
    $width (negedge CLR, 0:0:0, 0, notifier);
    $width (negedge I, 0:0:0, 0, notifier);
    $width (posedge CLR, 0:0:0, 0, notifier);
    $width (posedge I, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify
`endif
endmodule

`endcelldefine
