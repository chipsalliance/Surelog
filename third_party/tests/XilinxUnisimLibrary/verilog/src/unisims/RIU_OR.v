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
//  /   /                        RIU_OR
// /___/   /\      Filename    : RIU_OR.v
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

module RIU_OR #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter SIM_DEVICE = "ULTRASCALE",
  parameter real SIM_VERSION = 2.0
)(
  output [15:0] RIU_RD_DATA,
  output RIU_RD_VALID,

  input [15:0] RIU_RD_DATA_LOW,
  input [15:0] RIU_RD_DATA_UPP,
  input RIU_RD_VALID_LOW,
  input RIU_RD_VALID_UPP
);

// define constants
  localparam MODULE_NAME = "RIU_OR";

// Parameter encodings and registers
  localparam SIM_DEVICE_ULTRASCALE = 0;
  localparam SIM_DEVICE_ULTRASCALE_PLUS = 1;
  localparam SIM_DEVICE_ULTRASCALE_PLUS_ES1 = 2;
  localparam SIM_DEVICE_ULTRASCALE_PLUS_ES2 = 3;

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
//`ifdef XIL_DR
//  `include "RIU_OR_dr.v"
//`else
  localparam [152:1] SIM_DEVICE_REG = SIM_DEVICE;
  localparam real SIM_VERSION_REG = SIM_VERSION;
//`endif

  wire [1:0] SIM_DEVICE_BIN;
  wire [63:0] SIM_VERSION_BIN;

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif
  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR;

  wire RIU_RD_VALID_out;
  wire [15:0] RIU_RD_DATA_out;

  wire RIU_RD_VALID_LOW_in;
  wire RIU_RD_VALID_UPP_in;
  wire [15:0] RIU_RD_DATA_LOW_in;
  wire [15:0] RIU_RD_DATA_UPP_in;

  assign RIU_RD_DATA = RIU_RD_DATA_out;
  assign RIU_RD_VALID = RIU_RD_VALID_out;

  assign RIU_RD_DATA_LOW_in = RIU_RD_DATA_LOW;
  assign RIU_RD_DATA_UPP_in = RIU_RD_DATA_UPP;
  assign RIU_RD_VALID_LOW_in = RIU_RD_VALID_LOW;
  assign RIU_RD_VALID_UPP_in = RIU_RD_VALID_UPP;

  assign SIM_DEVICE_BIN =
      (SIM_DEVICE_REG == "ULTRASCALE") ? SIM_DEVICE_ULTRASCALE :
      (SIM_DEVICE_REG == "ULTRASCALE_PLUS") ? SIM_DEVICE_ULTRASCALE_PLUS :
      (SIM_DEVICE_REG == "ULTRASCALE_PLUS_ES1") ? SIM_DEVICE_ULTRASCALE_PLUS_ES1 :
      (SIM_DEVICE_REG == "ULTRASCALE_PLUS_ES2") ? SIM_DEVICE_ULTRASCALE_PLUS_ES2 :
       SIM_DEVICE_ULTRASCALE;
  
  assign SIM_VERSION_BIN = SIM_VERSION_REG * 1000;
  
  initial begin
    #1;
    trig_attr = ~trig_attr;
  end
  
  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2"))) begin
      $display("Error: [Unisim %s-101] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE, ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1 or ULTRASCALE_PLUS_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
       ((SIM_VERSION_REG != 2.0) &&
        (SIM_VERSION_REG != 1.0))) begin
      $display("Error: [Unisim %s-102] SIM_VERSION attribute is set to %f.  Legal values for this attribute are 2.0 or 1.0. Instance: %m", MODULE_NAME, SIM_VERSION_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end

  assign RIU_RD_DATA_out = RIU_RD_DATA_UPP_in | RIU_RD_DATA_LOW_in;
  assign RIU_RD_VALID_out =   RIU_RD_VALID_UPP_in & RIU_RD_VALID_LOW_in;

  specify
    (RIU_RD_DATA_LOW *> RIU_RD_DATA) = (0:0:0, 0:0:0);
    (RIU_RD_DATA_UPP *> RIU_RD_DATA) = (0:0:0, 0:0:0);
    (RIU_RD_VALID_LOW => RIU_RD_VALID) = (0:0:0, 0:0:0);
    (RIU_RD_VALID_UPP => RIU_RD_VALID) = (0:0:0, 0:0:0);
    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
