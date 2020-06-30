///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2015 Xilinx, Inc.
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
// \   \   \/      Version     : 2015.4
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        _no_description_
// /___/   /\      Filename    : OBUFDS_DPHY.v
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

module OBUFDS_DPHY #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter IOSTANDARD = "DEFAULT"
)(
  output O,
  output OB,

  input HSTX_I,
  input HSTX_T,
  input LPTX_I_N,
  input LPTX_I_P,
  input LPTX_T
);
  
// define constants
  localparam MODULE_NAME = "OBUFDS_DPHY";

// Parameter encodings and registers
  localparam IOSTANDARD_DEFAULT = 0;

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "OBUFDS_DPHY_dr.v"
`else
  localparam [56:1] IOSTANDARD_REG = IOSTANDARD;
`endif

  wire IOSTANDARD_BIN;

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif
  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR;

  reg OB_out;
  reg O_out;

  wire HSTX_I_in;
  wire HSTX_T_in;
  wire LPTX_I_N_in;
  wire LPTX_I_P_in;
  wire LPTX_T_in;

  reg hs_mode = 1'b1;

  assign (strong1,strong0) O = (hs_mode === 1'b0) ? O_out : 1'bz;
  assign (strong1, strong0) OB = (hs_mode === 1'b0) ? OB_out : 1'bz;
  assign (supply1,supply0) O = (hs_mode === 1'b1) ? O_out : 1'bz;
  assign (supply1,supply0) OB = (hs_mode === 1'b1) ? OB_out : 1'bz;

  assign HSTX_I_in = HSTX_I;
  assign HSTX_T_in = HSTX_T;
  assign LPTX_I_N_in = LPTX_I_N;
  assign LPTX_I_P_in = LPTX_I_P;
  assign LPTX_T_in = LPTX_T;

  assign IOSTANDARD_BIN =
    (IOSTANDARD_REG == "DEFAULT") ? IOSTANDARD_DEFAULT :
     IOSTANDARD_DEFAULT;
 
//Commenting out the DRC check for IOSTANDARD attribute as it is not required as per IOTST. 
/*  initial begin
    #1;
    trig_attr = ~trig_attr;
  end
  
  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((IOSTANDARD_REG != "DEFAULT"))) begin
      $display("Error: [Unisim %s-101] IOSTANDARD attribute is set to %s.  Legal values for this attribute are DEFAULT. Instance: %m", MODULE_NAME, IOSTANDARD_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end
*/
  always @ (LPTX_T_in or HSTX_T_in or LPTX_I_P_in or LPTX_I_N_in or HSTX_I_in) begin
    if (LPTX_T_in === 1'b0) begin
      O_out   <= LPTX_I_P_in;
      OB_out  <= LPTX_I_N_in;
      hs_mode <= 1'b0;
    end else if (LPTX_T_in === 1'b1 && HSTX_T_in === 1'b0) begin
      O_out   <= HSTX_I_in;
      OB_out  <= ~HSTX_I_in;
      hs_mode <= 1'b1;
    end else begin
      O_out   <= 1'bz;
      OB_out  <= 1'bz;
      hs_mode <= 1'bx;
    end
  end

specify
  (HSTX_I => O) = (0:0:0, 0:0:0);
  (HSTX_I => OB) = (0:0:0, 0:0:0);
  (HSTX_T => O) = (0:0:0, 0:0:0, 0:0:0, 0:0:0, 0:0:0, 0:0:0);
  (HSTX_T => OB) = (0:0:0, 0:0:0, 0:0:0, 0:0:0, 0:0:0, 0:0:0);
  (LPTX_I_N => OB) = (0:0:0, 0:0:0);
  (LPTX_I_P => O) = (0:0:0, 0:0:0);
  (LPTX_T => O) = (0:0:0, 0:0:0, 0:0:0, 0:0:0, 0:0:0, 0:0:0);
  (LPTX_T => OB) = (0:0:0, 0:0:0, 0:0:0, 0:0:0, 0:0:0, 0:0:0);
  specparam PATHPULSE$ = 0;
endspecify

endmodule

`endcelldefine
