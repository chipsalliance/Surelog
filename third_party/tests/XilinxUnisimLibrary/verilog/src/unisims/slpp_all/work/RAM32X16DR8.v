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
// \   \   \/      Version     : 2019.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        RAM32X16DR8
// /___/   /\      Filename    : RAM32X16DR8.v
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


module RAM32X16DR8 #(



  parameter [0:0] IS_WCLK_INVERTED = 1'b0
)(
  output DOA,
  output DOB,
  output DOC,
  output DOD,
  output DOE,
  output DOF,
  output DOG,
  output [1:0] DOH,

  input [5:0] ADDRA,
  input [5:0] ADDRB,
  input [5:0] ADDRC,
  input [5:0] ADDRD,
  input [5:0] ADDRE,
  input [5:0] ADDRF,
  input [5:0] ADDRG,
  input [4:0] ADDRH,
  input [1:0] DIA,
  input [1:0] DIB,
  input [1:0] DIC,
  input [1:0] DID,
  input [1:0] DIE,
  input [1:0] DIF,
  input [1:0] DIG,
  input [1:0] DIH,
  input WCLK,
  input WE
);

// define constants
  localparam MODULE_NAME = "RAM32X16DR8";
  
  reg trig_attr;
// include dynamic registers - XILINX test only



  reg [0:0] IS_WCLK_INVERTED_REG = IS_WCLK_INVERTED;





tri0 glblGSR = glbl.GSR;


  wire WCLK_in;
  wire WE_in;
  wire [1:0] DIA_in;
  wire [1:0] DIB_in;
  wire [1:0] DIC_in;
  wire [1:0] DID_in;
  wire [1:0] DIE_in;
  wire [1:0] DIF_in;
  wire [1:0] DIG_in;
  wire [1:0] DIH_in;
  wire [4:0] ADDRH_in;
  wire [5:0] ADDRA_in;
  wire [5:0] ADDRB_in;
  wire [5:0] ADDRC_in;
  wire [5:0] ADDRD_in;
  wire [5:0] ADDRE_in;
  wire [5:0] ADDRF_in;
  wire [5:0] ADDRG_in;







































  assign ADDRA_in = ADDRA;
  assign ADDRB_in = ADDRB;
  assign ADDRC_in = ADDRC;
  assign ADDRD_in = ADDRD;
  assign ADDRE_in = ADDRE;
  assign ADDRF_in = ADDRF;
  assign ADDRG_in = ADDRG;
  assign ADDRH_in = ADDRH;
  assign DIA_in = DIA;
  assign DIB_in = DIB;
  assign DIC_in = DIC;
  assign DID_in = DID;
  assign DIE_in = DIE;
  assign DIF_in = DIF;
  assign DIG_in = DIG;
  assign DIH_in = DIH;
  assign WCLK_in = WCLK ^ IS_WCLK_INVERTED_REG;
  assign WE_in = (WE === 1'bz) || WE; // rv 1



  initial begin
  trig_attr = 1'b0;
  #1;
  trig_attr = ~trig_attr;
end


// begin behavioral model

  reg [63:0] mem_a, mem_b, mem_c, mem_d;
  reg [63:0] mem_e, mem_f, mem_g, mem_h;
  reg [5:0]  addr_in1, addr_in2;

  always @(ADDRH_in) begin
      addr_in1 = 2 * ADDRH_in;
      addr_in2 = 2 * ADDRH_in + 1;
  end

  always @(posedge WCLK_in)
    if (WE_in) begin
      mem_a[addr_in1] <= #100 DIA_in[0];
      mem_a[addr_in2] <= #100 DIA_in[1];
      mem_b[addr_in1] <= #100 DIB_in[0];
      mem_b[addr_in2] <= #100 DIB_in[1];
      mem_c[addr_in1] <= #100 DIC_in[0];
      mem_c[addr_in2] <= #100 DIC_in[1];
      mem_d[addr_in1] <= #100 DID_in[0];
      mem_d[addr_in2] <= #100 DID_in[1];
      mem_e[addr_in1] <= #100 DIE_in[0];
      mem_e[addr_in2] <= #100 DIE_in[1];
      mem_f[addr_in1] <= #100 DIF_in[0];
      mem_f[addr_in2] <= #100 DIF_in[1];
      mem_g[addr_in1] <= #100 DIG_in[0];
      mem_g[addr_in2] <= #100 DIG_in[1];
      mem_h[addr_in1] <= #100 DIH_in[0];
      mem_h[addr_in2] <= #100 DIH_in[1];
  end

   assign  DOA    = mem_a[ADDRA_in];
   assign  DOB    = mem_b[ADDRB_in];
   assign  DOC    = mem_c[ADDRC_in];
   assign  DOD    = mem_d[ADDRD_in];
   assign  DOE    = mem_e[ADDRE_in];
   assign  DOF    = mem_f[ADDRF_in];
   assign  DOG    = mem_g[ADDRG_in];
   assign  DOH[0] = mem_h[2*ADDRH_in];
   assign  DOH[1] = mem_h[2*ADDRH_in + 1];


// end behavioral model












































































































































endmodule

`endcelldefine

