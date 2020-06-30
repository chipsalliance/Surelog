///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2019 Xilinx, Inc.
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
//  /   /                        BUFG_GT
// /___/   /\      Filename    : BUFG_GT.v
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

module BUFG_GT #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter SIM_DEVICE = "ULTRASCALE",
  parameter STARTUP_SYNC = "FALSE"
)(
  output O,

  input CE,
  input CEMASK,
  input CLR,
  input CLRMASK,
  input [2:0] DIV,
  input I
);
  
// define constants
  localparam MODULE_NAME = "BUFG_GT";

// Parameter encodings and registers
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
  `include "BUFG_GT_dr.v"
`else
  reg [144:1] SIM_DEVICE_REG = SIM_DEVICE;
  reg [40:1] STARTUP_SYNC_REG = STARTUP_SYNC;
`endif

`ifdef XIL_XECLIB
  wire [4:0] SIM_DEVICE_BIN;
  wire STARTUP_SYNC_BIN;
`else
  reg [4:0] SIM_DEVICE_BIN;
  reg STARTUP_SYNC_BIN;
`endif

`ifdef XIL_XECLIB
  reg glblGSR = 1'b0;
`else
  tri0 glblGSR = glbl.GSR;
`endif

  wire CEMASK_in;
  wire CE_in;
  wire CLRMASK_in;
  wire CLR_in;
  wire I_in;
  wire [2:0] DIV_in;

  assign CEMASK_in = (CEMASK !== 1'bz) && CEMASK; // rv 0
  assign CE_in = (CE === 1'bz) || CE; // rv 1
  assign CLRMASK_in = (CLRMASK !== 1'bz) && CLRMASK; // rv 0
  assign CLR_in = (CLR !== 1'bz) && CLR; // rv 0
  assign DIV_in[0] = (DIV[0] !== 1'bz) && DIV[0]; // rv 0
  assign DIV_in[1] = (DIV[1] !== 1'bz) && DIV[1]; // rv 0
  assign DIV_in[2] = (DIV[2] !== 1'bz) && DIV[2]; // rv 0
  assign I_in = I;

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
      $display("Error: [Unisim %s-101] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE, ULTRASCALE_PLUS, VERSAL_AI_CORE, VERSAL_AI_CORE_ES1, VERSAL_AI_CORE_ES2, VERSAL_AI_EDGE, VERSAL_AI_EDGE_ES1, VERSAL_AI_EDGE_ES2, VERSAL_AI_RF, VERSAL_AI_RF_ES1, VERSAL_AI_RF_ES2, VERSAL_HBM, VERSAL_HBM_ES1, VERSAL_HBM_ES2, VERSAL_PREMIUM, VERSAL_PREMIUM_ES1, VERSAL_PREMIUM_ES2, VERSAL_PRIME, VERSAL_PRIME_ES1 or VERSAL_PRIME_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((STARTUP_SYNC_REG != "FALSE") &&
         (STARTUP_SYNC_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-102] STARTUP_SYNC attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, STARTUP_SYNC_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end //always

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
  end //always

`endif

`ifdef XIL_TIMING
  reg notifier;
`endif

// begin behavioral model

  integer   clk_count=1, first_toggle_count=1, second_toggle_count=1;
  reg       first_rise = 1'b0, first_half_period = 1'b0;
  reg       O_bufg_gt = 0;
  reg       O_bufg_gt_dev = 0;
  wire      i_ce, i_inv, clr_inv ;
  wire      ce_masked, clrmask_inv, clr_masked;
  reg       ce_en = 1'b0;
  reg       ce_sync1  = 1'b0;
  reg       ce_sync2  = 1'b0; 
  reg       clr_sync1 = 1'b0;
  reg       clr_sync2 = 1'b0;
  wire      ce_sync;
  wire      clr_sync;
  reg [2:0] gwe_sync;
  wire      gsr_muxed_sync;
  reg       sim_device_versal_or_later;

  initial begin
    gwe_sync                   = 3'b000;
    sim_device_versal_or_later = 1'b0;
  end

  always @ (trig_attr) begin
    #1;
    if ((SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_AI_CORE      ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_AI_CORE_ES1  ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_AI_CORE_ES2  ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_AI_EDGE      ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_AI_EDGE_ES1  ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_AI_EDGE_ES2  ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_AI_RF        ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_AI_RF_ES1    ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_AI_RF_ES2    ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_HBM          ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_HBM_ES1      ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_HBM_ES2      ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_PREMIUM      ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_PREMIUM_ES1  ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_PREMIUM_ES2  ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_PRIME        ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_PRIME_ES1    ) ||
        (SIM_DEVICE_BIN == SIM_DEVICE_VERSAL_PRIME_ES2    ))
      sim_device_versal_or_later <= 1'b1;
    else 
      sim_device_versal_or_later <= 1'b0;
  end //always

  always @(posedge I_in) begin
    if(I_in==1'b1)
      gwe_sync <= {gwe_sync[1:0], ~glblGSR};
  end

  assign gsr_muxed_sync = (STARTUP_SYNC_BIN == STARTUP_SYNC_TRUE) ? ~gwe_sync[2] :  glblGSR;

  always@(DIV_in) begin
    case (DIV_in)
      3'b000 : begin
                 first_toggle_count = 1;
                 second_toggle_count = 1;
               end
      3'b001 : begin
                 first_toggle_count = 2;
                 second_toggle_count = 2;
               end
      3'b010 : begin
                 first_toggle_count = 2;
                 second_toggle_count = 4;
               end
      3'b011 : begin
                 first_toggle_count = 4;
                 second_toggle_count = 4;
               end
      3'b100 : begin
                 first_toggle_count = 4;
                 second_toggle_count = 6;
               end
      3'b101 : begin
                 first_toggle_count = 6;
                 second_toggle_count = 6;
               end
      3'b110 : begin
                 first_toggle_count = 6;
                 second_toggle_count = 8;
               end
      3'b111 : begin
                 first_toggle_count = 8;
                 second_toggle_count = 8;
               end
    endcase // case(BUFG_GT)

  end 

  always begin
    if (gsr_muxed_sync == 1'b1) begin
      assign O_bufg_gt = 1'b0;
      assign clk_count = 0;
      assign first_rise = 1'b1;
      assign first_half_period = 1'b0;
    end
    else if (gsr_muxed_sync == 1'b0) begin
      deassign O_bufg_gt;
      deassign clk_count;
      deassign first_rise;
      deassign first_half_period;
    end
    @(gsr_muxed_sync);
  end

  always @(posedge I_in, posedge gsr_muxed_sync)
  begin
    if (gsr_muxed_sync == 1'b1)
    begin
      ce_sync1 <= 1'b0;
      ce_sync2 <= 1'b0;
    end
    else
    begin
      ce_sync1 <= CE_in;
      ce_sync2 <= ce_sync1;
    end
  end

  assign ce_sync =  sim_device_versal_or_later ? CE_in :  ce_sync2;

  assign clr_inv = ~CLR_in;

  always @(posedge I_in, negedge clr_inv)
  begin
    if(~clr_inv)
    begin
      clr_sync1 <= 1'b0;
      clr_sync2  <= 1'b0;
    end
    else
      {clr_sync2, clr_sync1} <= {clr_sync1, 1'b1};
  end
  assign clr_sync = sim_device_versal_or_later ? clr_inv : clr_sync2;

  assign i_inv = ~I_in;
  assign clrmask_inv = ~CLRMASK_in;
  assign ce_masked = ce_sync | CEMASK_in;
  assign clr_masked = ~clr_sync & clrmask_inv;

  always @(i_inv, gsr_muxed_sync, ce_masked, clr_masked)
  begin
    if (gsr_muxed_sync || clr_masked)
      ce_en <= 1'b0;
    else if (i_inv)
      ce_en <= ce_masked;
  end

  assign i_ce = I_in & ce_en;

  always @(i_ce or posedge gsr_muxed_sync or posedge clr_masked) begin
    if (first_toggle_count == 1) begin
      O_bufg_gt = i_ce;
    end
    else begin
      if(clr_masked == 1'b1 || gsr_muxed_sync == 1'b1) begin
        O_bufg_gt = 1'b0;
        clk_count = 1;
        first_half_period = 1'b1;
        first_rise = 1'b1;
      end
      else if(clr_masked == 1'b0 && gsr_muxed_sync == 1'b0) begin
        if (i_ce == 1'b1 && first_rise == 1'b1) begin
          O_bufg_gt = 1'b1;
          clk_count = 1;
          first_half_period = 1'b1;
          first_rise = 1'b0;
        end
        else if (clk_count == second_toggle_count && first_half_period == 1'b0) begin
          O_bufg_gt = ~O_bufg_gt;
          clk_count = 1;
          first_half_period = 1'b1;
        end
        else if (clk_count == first_toggle_count && first_half_period == 1'b1) begin
          O_bufg_gt = ~O_bufg_gt;
          clk_count = 1;
          first_half_period = 1'b0;
        end
        else if (first_rise == 1'b0) begin
          clk_count = clk_count + 1;
        end
      end
    end
  end

  // assign #1 O =   O_bufg_gt;
     
  always @(*) begin
    if(sim_device_versal_or_later)
      O_bufg_gt_dev <= O_bufg_gt;
    else
      O_bufg_gt_dev <= #1 O_bufg_gt;
  end

  assign O = O_bufg_gt_dev;


// end behavioral model

`ifndef XIL_XECLIB
`ifdef XIL_TIMING
  specify
    (I => O) = (0:0:0, 0:0:0);
    $period (negedge I, 0:0:0, notifier);
    $period (posedge I, 0:0:0, notifier);
    $width (negedge CLR, 0:0:0, 0, notifier);
    $width (negedge I, 0:0:0, 0, notifier);
    $width (posedge CLR, 0:0:0, 0, notifier);
    $width (posedge I, 0:0:0, 0, notifier);
    specparam PATHPULSE$ = 0;
  endspecify
`endif
`endif
endmodule

`endcelldefine
