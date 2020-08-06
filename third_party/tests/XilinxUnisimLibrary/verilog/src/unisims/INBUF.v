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
//  /   /                        
// /___/   /\      Filename    : INBUF.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//
//    10/22/14 808642 Added #1 to $finish
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module INBUF #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter IBUF_LOW_PWR = "TRUE",
  parameter ISTANDARD = "UNUSED",
  parameter integer SIM_INPUT_BUFFER_OFFSET = 0
)(
  output O,

  input [3:0] OSC,
  input OSC_EN,
  input PAD,
  input VREF
);

// define constants
  localparam MODULE_NAME = "INBUF";

// Parameter encodings and registers
  localparam IBUF_LOW_PWR_FALSE = 1;
  localparam IBUF_LOW_PWR_TRUE = 0;

  reg trig_attr = 1'b0;
  localparam [40:1] IBUF_LOW_PWR_REG = IBUF_LOW_PWR;
  localparam integer SIM_INPUT_BUFFER_OFFSET_REG = SIM_INPUT_BUFFER_OFFSET;

  wire IBUF_LOW_PWR_BIN;
  wire [6:0] SIM_INPUT_BUFFER_OFFSET_BIN;

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif
  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR;

  wire OSC_EN_in;
  wire [3:0] OSC_in;

`ifdef XIL_TIMING
  wire OSC_EN_delay;
  wire [3:0] OSC_delay;
`endif

  reg O_OSC_in;
  integer OSC_int = 0; 

  assign O = (OSC_EN_in === 1'b1) ? O_OSC_in : PAD;

`ifdef XIL_TIMING
  assign OSC_EN_in = OSC_EN_delay;
  assign OSC_in = OSC_delay;
`else
  assign OSC_EN_in = OSC_EN;
  assign OSC_in = OSC;
`endif

  assign IBUF_LOW_PWR_BIN =
      (IBUF_LOW_PWR_REG == "TRUE") ? IBUF_LOW_PWR_TRUE :
      (IBUF_LOW_PWR_REG == "FALSE") ? IBUF_LOW_PWR_FALSE :
       IBUF_LOW_PWR_TRUE;
  
`ifndef XIL_TIMING
  initial begin
    $display("Error: [Unisim %s-106] SIMPRIM primitive is not intended for direct instantiation in RTL or functional netlists. This primitive is only available in the SIMPRIM library for implemented netlists, please ensure you are pointing to the correct library. Instance %m", MODULE_NAME);
    #1 $finish;
  end
`endif

  initial begin
    #1;
    trig_attr = ~trig_attr;
  end
  
  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((SIM_INPUT_BUFFER_OFFSET_REG < -50) || (SIM_INPUT_BUFFER_OFFSET_REG > 50))) begin
      $display("Error: [Unisim %s-111] SIM_INPUT_BUFFER_OFFSET attribute is set to %d.  Legal values for this attribute are -50 to 50. Instance: %m", MODULE_NAME, SIM_INPUT_BUFFER_OFFSET_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((IBUF_LOW_PWR_REG != "TRUE") &&
         (IBUF_LOW_PWR_REG != "FALSE"))) begin
      $display("Error: [Unisim %s-104] IBUF_LOW_PWR attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, IBUF_LOW_PWR_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end

  always @ (OSC_in or OSC_EN_in) begin
   OSC_int = OSC_in[2:0] * 5;
   if (OSC_in[3] == 1'b0 )
      OSC_int =  -1*OSC_int;

   if(OSC_EN_in === 1'b1) begin
    if ((SIM_INPUT_BUFFER_OFFSET_REG - OSC_int) < 0) begin
        O_OSC_in <= 1'b0;
    end else if ((SIM_INPUT_BUFFER_OFFSET_REG - OSC_int) > 0) begin  
        O_OSC_in <= 1'b1;
    end else if ((SIM_INPUT_BUFFER_OFFSET_REG - OSC_int) == 0) begin
        O_OSC_in <= ~O_OSC_in;
    end  
   end
  end

  initial begin
// if (OSC_EN_in === 1'b1) begin
    if ((SIM_INPUT_BUFFER_OFFSET_REG - OSC_int) < 0) begin
        O_OSC_in <= 1'b0;
    end else if ((SIM_INPUT_BUFFER_OFFSET_REG - OSC_int) > 0) begin  
        O_OSC_in <= 1'b1;
    end else if ((SIM_INPUT_BUFFER_OFFSET_REG - OSC_int) == 0) begin
        O_OSC_in <= 1'bx;
    end  
  end

`ifdef XIL_TIMING
  reg notifier;
`endif

  specify
    (OSC *> O) = (0:0:0, 0:0:0);
    (OSC_EN => O) = (0:0:0, 0:0:0);
    (PAD => O) = (0:0:0, 0:0:0);
`ifdef XIL_TIMING
    $setuphold (negedge OSC_EN, negedge OSC, 0:0:0, 0:0:0, notifier, , , OSC_EN_delay, OSC_delay);
    $setuphold (negedge OSC_EN, posedge OSC, 0:0:0, 0:0:0, notifier, , , OSC_EN_delay, OSC_delay);
`endif
    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
