///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2014 Xilinx, Inc.
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
// /___/  \  /    Vendor : Xilinx
// \   \   \/     Version : 2014.3
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                  Static Dual Port Synchronous RAM 256-Deep by 1-Wide
// /___/   /\     Filename : RAM256X1D.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//    07/02/12 - Initial version, from RAM128X1D
//    10/22/14 - Added #1 to $finish (CR 808642).
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps


`celldefine


module RAM256X1D #(



    parameter [255:0] INIT = 256'h0,
    parameter [0:0] IS_WCLK_INVERTED = 1'b0
) (
    output DPO,
    output SPO,

    input [7:0] A,
    input D,
    input [7:0] DPRA,
    input WCLK,
    input WE
);

// define constants
  localparam MODULE_NAME = "RAM256X1D";

  reg trig_attr = 1'b0;




  reg attr_test = 1'b0;

  reg attr_err = 1'b0;

  wire IS_WCLK_INVERTED_BIN;

  wire D_in;
  wire WCLK_in;
  wire WE_in;
  wire [7:0] A_in;
  wire [7:0] DPRA_in;

  assign IS_WCLK_INVERTED_BIN = IS_WCLK_INVERTED;


















  assign A_in = A;
  assign D_in = D;
  assign WCLK_in = WCLK ^ IS_WCLK_INVERTED_BIN;
  assign WE_in = (WE === 1'bz) || WE; // rv 1

  assign DPRA_in = DPRA;
    
  reg  [255:0] mem;

  initial 
    mem = INIT;

  assign DPO = mem[DPRA_in];
  assign SPO = mem[A_in];

  always @(posedge WCLK_in) 
    if (WE_in == 1'b1) mem[A_in] <= #100 D_in;
    







































































    
endmodule

`endcelldefine

