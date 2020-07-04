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
// /___/  \  /    Vendor      : Xilinx
// \   \   \/     Version     : 2014.3
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                       32-Deep by 8-bit Wide Multi Port RAM 
// /___/   /\     Filename    : RAM32M.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//    03/21/06 - Initial version.
//    12/01/06 - Fix cut/past error for port C and D (CR 430051)
//    05/07/08 - Add negative setup/hold support (CR468872)
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//    04/18/13 - PR683925 - add invertible pin support.
//    10/22/14 - Added #1 to $finish (CR 808642).
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module RAM32M #(



  parameter [63:0] INIT_A = 64'h0000000000000000,
  parameter [63:0] INIT_B = 64'h0000000000000000,
  parameter [63:0] INIT_C = 64'h0000000000000000,
  parameter [63:0] INIT_D = 64'h0000000000000000,
  parameter [0:0] IS_WCLK_INVERTED = 1'b0
)(
  output [1:0] DOA,
  output [1:0] DOB,
  output [1:0] DOC,
  output [1:0] DOD,

  input [4:0] ADDRA,
  input [4:0] ADDRB,
  input [4:0] ADDRC,
  input [4:0] ADDRD,
  input [1:0] DIA,
  input [1:0] DIB,
  input [1:0] DIC,
  input [1:0] DID,
  input WCLK,
  input WE
);
  
// define constants
  localparam MODULE_NAME = "RAM32M";

  reg trig_attr = 1'b0;




  reg attr_test = 1'b0;

  reg attr_err = 1'b0;

  wire IS_WCLK_INVERTED_BIN;

  wire [4:0] ADDRD_in;
  wire [1:0] DIA_in;
  wire [1:0] DIB_in;
  wire [1:0] DIC_in;
  wire [1:0] DID_in;
  wire WCLK_in;
  wire WE_in;
























  assign ADDRD_in = ADDRD;
  assign DIA_in = DIA;
  assign DIB_in = DIB;
  assign DIC_in = DIC;
  assign DID_in = DID;
  assign WCLK_in = WCLK ^ IS_WCLK_INVERTED_BIN;
  assign WE_in = (WE === 1'bz) || WE; // rv 1

    
  assign IS_WCLK_INVERTED_BIN = IS_WCLK_INVERTED;

  reg [63:0] mem_a, mem_b, mem_c, mem_d;
  reg [5:0] addr_in2, addr_in1;

  initial begin
    mem_a = INIT_A;
    mem_b = INIT_B;
    mem_c = INIT_C;
    mem_d = INIT_D;
  end

  always @(ADDRD_in) begin
      addr_in2 = 2 * ADDRD_in;
      addr_in1 = 2 * ADDRD_in + 1;
  end

  always @(posedge WCLK_in)
    if (WE_in) begin
      mem_a[addr_in2] <= #100 DIA_in[0];
      mem_a[addr_in1] <= #100 DIA_in[1];
      mem_b[addr_in2] <= #100 DIB_in[0];
      mem_b[addr_in1] <= #100 DIB_in[1];
      mem_c[addr_in2] <= #100 DIC_in[0];
      mem_c[addr_in1] <= #100 DIC_in[1];
      mem_d[addr_in2] <= #100 DID_in[0];
      mem_d[addr_in1] <= #100 DID_in[1];
  end

   assign  DOA[0] = mem_a[2*ADDRA];
   assign  DOA[1] = mem_a[2*ADDRA + 1];
   assign  DOB[0] = mem_b[2*ADDRB];
   assign  DOB[1] = mem_b[2*ADDRB + 1];
   assign  DOC[0] = mem_c[2*ADDRC];
   assign  DOC[1] = mem_c[2*ADDRC + 1];
   assign  DOD[0] = mem_d[2*ADDRD_in];
   assign  DOD[1] = mem_d[2*ADDRD_in + 1];

































































































endmodule

`endcelldefine
