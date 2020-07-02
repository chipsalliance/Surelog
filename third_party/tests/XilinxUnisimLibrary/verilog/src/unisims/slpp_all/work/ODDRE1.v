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
// \   \   \/      Version     : 2019.2
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        ODDRE1
// /___/   /\      Filename    : ODDRE1.v
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

module ODDRE1 #(



  parameter [0:0] IS_C_INVERTED = 1'b0,
  parameter [0:0] IS_D1_INVERTED = 1'b0,
  parameter [0:0] IS_D2_INVERTED = 1'b0,
  parameter SIM_DEVICE = "ULTRASCALE",
  parameter [0:0] SRVAL = 1'b0
)(
  output Q,

  input C,
  input D1,
  input D2,
  input SR
);

// define constants
  localparam MODULE_NAME = "ODDRE1";
  
// Parameter encodings and registers
  localparam SIM_DEVICE_ULTRASCALE = 0;
  localparam SIM_DEVICE_ULTRASCALE_PLUS = 1;
  localparam SIM_DEVICE_ULTRASCALE_PLUS_ES1 = 2;
  localparam SIM_DEVICE_ULTRASCALE_PLUS_ES2 = 3;
  localparam SIM_DEVICE_VERSAL_AI_CORE = 5;
  localparam SIM_DEVICE_VERSAL_AI_CORE_ES1 = 6;
  localparam SIM_DEVICE_VERSAL_AI_CORE_ES2 = 7;
  localparam SIM_DEVICE_VERSAL_AI_EDGE = 8;
  localparam SIM_DEVICE_VERSAL_AI_EDGE_ES1 = 9;
  localparam SIM_DEVICE_VERSAL_AI_EDGE_ES2 = 10;
  localparam SIM_DEVICE_VERSAL_AI_RF = 11;
  localparam SIM_DEVICE_VERSAL_AI_RF_ES1 = 12;
  localparam SIM_DEVICE_VERSAL_AI_RF_ES2 = 13;
  localparam SIM_DEVICE_VERSAL_HBM = 16;
  localparam SIM_DEVICE_VERSAL_HBM_ES1 = 17;
  localparam SIM_DEVICE_VERSAL_HBM_ES2 = 18;
  localparam SIM_DEVICE_VERSAL_PREMIUM = 19;
  localparam SIM_DEVICE_VERSAL_PREMIUM_ES1 = 20;
  localparam SIM_DEVICE_VERSAL_PREMIUM_ES2 = 21;
  localparam SIM_DEVICE_VERSAL_PRIME = 22;
  localparam SIM_DEVICE_VERSAL_PRIME_ES1 = 23;
  localparam SIM_DEVICE_VERSAL_PRIME_ES2 = 24;

  reg trig_attr;
// include dynamic registers - XILINX test only



  reg [0:0] IS_C_INVERTED_REG = IS_C_INVERTED;
  reg [0:0] IS_D1_INVERTED_REG = IS_D1_INVERTED;
  reg [0:0] IS_D2_INVERTED_REG = IS_D2_INVERTED;
  reg [152:1] SIM_DEVICE_REG = SIM_DEVICE;
  reg [0:0] SRVAL_REG = SRVAL;





  reg [4:0] SIM_DEVICE_BIN;





tri0 glblGSR = glbl.GSR;


  wire C_in;
  wire D1_in;
  wire D2_in;
  wire SR_in;













  assign C_in = C ^ IS_C_INVERTED_REG;
  assign D1_in = D1 ^ IS_D1_INVERTED_REG;
  assign D2_in = D2 ^ IS_D2_INVERTED_REG;
  assign SR_in = (SR !== 1'bz) && SR; // rv 0



  reg attr_test;
  reg attr_err;
  
  initial begin
  trig_attr = 1'b0;
  


    attr_test = 1'b0;
  
    attr_err = 1'b0;
    #1;
    trig_attr = ~trig_attr;
  end





























  always @ (trig_attr) begin
  #1;
  SIM_DEVICE_BIN =
      (SIM_DEVICE_REG == "ULTRASCALE") ? SIM_DEVICE_ULTRASCALE :
      (SIM_DEVICE_REG == "ULTRASCALE_PLUS") ? SIM_DEVICE_ULTRASCALE_PLUS :
      (SIM_DEVICE_REG == "ULTRASCALE_PLUS_ES1") ? SIM_DEVICE_ULTRASCALE_PLUS_ES1 :
      (SIM_DEVICE_REG == "ULTRASCALE_PLUS_ES2") ? SIM_DEVICE_ULTRASCALE_PLUS_ES2 :
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
  
  end



  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2") &&
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
      $display("Error: [Unisim %s-105] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE, ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1, ULTRASCALE_PLUS_ES2, VERSAL_AI_CORE, VERSAL_AI_CORE_ES1, VERSAL_AI_CORE_ES2, VERSAL_AI_EDGE, VERSAL_AI_EDGE_ES1, VERSAL_AI_EDGE_ES2, VERSAL_AI_RF, VERSAL_AI_RF_ES1, VERSAL_AI_RF_ES2, VERSAL_HBM, VERSAL_HBM_ES1, VERSAL_HBM_ES2, VERSAL_PREMIUM, VERSAL_PREMIUM_ES1, VERSAL_PREMIUM_ES2, VERSAL_PRIME, VERSAL_PRIME_ES1 or VERSAL_PRIME_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end






// begin behavioral model

  reg Q_out;
  reg QD2_posedge_int;
  reg R_sync1 = 1'b0;
  reg R_sync2 = 1'b0;
  reg R_sync3 = 1'b0;
  wire R_sync;
  wire R_async;

  assign Q = Q_out;
  assign R_async = ((SIM_DEVICE_BIN != SIM_DEVICE_ULTRASCALE) && (SIM_DEVICE_BIN != SIM_DEVICE_ULTRASCALE_PLUS) && (SIM_DEVICE_BIN != SIM_DEVICE_ULTRASCALE_PLUS_ES1) && (SIM_DEVICE_BIN != SIM_DEVICE_ULTRASCALE_PLUS_ES2));
  assign R_sync = R_async ? SR_in : (R_sync1 || R_sync2 || R_sync3);

  always @(posedge C_in) begin
    if (~R_async) begin
      R_sync1 <= SR_in;
      R_sync2 <= R_sync1;
      R_sync3 <= R_sync2;
    end
  end
  
  always @ (glblGSR or SR_in or R_sync) begin
    if (glblGSR == 1'b1) begin
      assign Q_out = SRVAL_REG;
      assign QD2_posedge_int = SRVAL_REG;
    end else if (glblGSR == 1'b0) begin
      if (SR_in == 1'b1 || R_sync == 1'b1) begin
        assign Q_out = SRVAL_REG;
        assign QD2_posedge_int = SRVAL_REG;
      end else if (R_sync == 1'b0) begin
        deassign Q_out;
        deassign QD2_posedge_int;
      end
    end
  end
 
  always @(posedge C_in) begin
    if (SR_in == 1'b1 || R_sync ==1'b1) begin
      Q_out <= SRVAL_REG;
      QD2_posedge_int <= SRVAL_REG;
    end else if (R_sync == 1'b0) begin
      Q_out <= D1_in;
      QD2_posedge_int <= D2_in;
    end
  end

  always @(negedge C_in) begin
    if (SR_in == 1'b1 || R_sync == 1'b1) begin
      Q_out <= SRVAL_REG;
    end else if (R_sync == 1'b0) begin
      Q_out <= QD2_posedge_int;
    end
  end

// end behavioral model












  specify
    (C => Q) = (100:100:100, 100:100:100);
    (D1 => Q) = (0:0:0, 0:0:0);
    (posedge SR => (Q +: 0)) = (100:100:100, 100:100:100);
    (posedge SR => (Q +: 1)) = (100:100:100, 100:100:100);




















    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
