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
// \   \   \/      Version     : 2018.3
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        DSP_PREADD_DATA
// /___/   /\      Filename    : DSP_PREADD_DATA.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//  07/15/12 - Migrate from E1.
//  12/10/12 - Add dynamic registers
//  01/11/13 - DIN, D_DATA data width change (26/24) sync4 yml
//  04/23/13 - 714772 - remove sensitivity to negedge GSR
//  05/07/13 - 716896 - INMODE_INV_REG mis sized
//  10/22/14 - 808642 - Added #1 to $finish
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module DSP_PREADD_DATA #(



  parameter integer ADREG = 1,
  parameter AMULTSEL = "A",
  parameter BMULTSEL = "B",
  parameter integer DREG = 1,
  parameter integer INMODEREG = 1,
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [4:0] IS_INMODE_INVERTED = 5'b00000,
  parameter [0:0] IS_RSTD_INVERTED = 1'b0,
  parameter [0:0] IS_RSTINMODE_INVERTED = 1'b0,
  parameter PREADDINSEL = "A",
  parameter USE_MULT = "MULTIPLY"
)(
  output [26:0] A2A1,
  output ADDSUB,
  output [26:0] AD_DATA,
  output [17:0] B2B1,
  output [26:0] D_DATA,
  output INMODE_2,
  output [26:0] PREADD_AB,

  input [26:0] A1_DATA,
  input [26:0] A2_DATA,
  input [26:0] AD,
  input [17:0] B1_DATA,
  input [17:0] B2_DATA,
  input CEAD,
  input CED,
  input CEINMODE,
  input CLK,
  input [26:0] DIN,
  input [4:0] INMODE,
  input RSTD,
  input RSTINMODE
);
  
// define constants
  localparam MODULE_NAME = "DSP_PREADD_DATA";

// Parameter encodings and registers
  localparam AMULTSEL_A = 0;
  localparam AMULTSEL_AD = 1;
  localparam BMULTSEL_AD = 1;
  localparam BMULTSEL_B = 0;
  localparam PREADDINSEL_A = 0;
  localparam PREADDINSEL_B = 1;
  localparam USE_MULT_DYNAMIC = 1;
  localparam USE_MULT_MULTIPLY = 0;
  localparam USE_MULT_NONE = 2;

  reg trig_attr;
// include dynamic registers - XILINX test only



  reg [31:0] ADREG_REG = ADREG;
  reg [16:1] AMULTSEL_REG = AMULTSEL;
  reg [16:1] BMULTSEL_REG = BMULTSEL;
  reg [31:0] DREG_REG = DREG;
  reg [31:0] INMODEREG_REG = INMODEREG;
  reg [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
  reg [4:0] IS_INMODE_INVERTED_REG = IS_INMODE_INVERTED;
  reg [0:0] IS_RSTD_INVERTED_REG = IS_RSTD_INVERTED;
  reg [0:0] IS_RSTINMODE_INVERTED_REG = IS_RSTINMODE_INVERTED;
  reg [8:1] PREADDINSEL_REG = PREADDINSEL;
  reg [64:1] USE_MULT_REG = USE_MULT;











  reg ADREG_BIN;
  reg AMULTSEL_BIN;
  reg BMULTSEL_BIN;
  reg DREG_BIN;
  reg INMODEREG_BIN;
  reg PREADDINSEL_BIN;
  reg [1:0] USE_MULT_BIN;





  tri0 glblGSR = glbl.GSR;


  wire CEAD_in;
  wire CED_in;
  wire CEINMODE_in;
  wire CLK_in;
  wire RSTD_in;
  wire RSTINMODE_in;
  wire [17:0] B1_DATA_in;
  wire [17:0] B2_DATA_in;
  wire [26:0] A1_DATA_in;
  wire [26:0] A2_DATA_in;
  wire [26:0] AD_in;
  wire [26:0] DIN_in;
  wire [4:0] INMODE_in;












  




  assign AD_in = AD;
  assign CEAD_in = (CEAD !== 1'bz) && CEAD; // rv 0
  assign CED_in = (CED !== 1'bz) && CED; // rv 0
  assign CEINMODE_in = CEINMODE;
  assign CLK_in = (CLK !== 1'bz) && (CLK ^ IS_CLK_INVERTED_REG); // rv 0
  assign DIN_in[0] = (DIN[0] !== 1'bz) && DIN[0]; // rv 0
  assign DIN_in[10] = (DIN[10] !== 1'bz) && DIN[10]; // rv 0
  assign DIN_in[11] = (DIN[11] !== 1'bz) && DIN[11]; // rv 0
  assign DIN_in[12] = (DIN[12] !== 1'bz) && DIN[12]; // rv 0
  assign DIN_in[13] = (DIN[13] !== 1'bz) && DIN[13]; // rv 0
  assign DIN_in[14] = (DIN[14] !== 1'bz) && DIN[14]; // rv 0
  assign DIN_in[15] = (DIN[15] !== 1'bz) && DIN[15]; // rv 0
  assign DIN_in[16] = (DIN[16] !== 1'bz) && DIN[16]; // rv 0
  assign DIN_in[17] = (DIN[17] !== 1'bz) && DIN[17]; // rv 0
  assign DIN_in[18] = (DIN[18] !== 1'bz) && DIN[18]; // rv 0
  assign DIN_in[19] = (DIN[19] !== 1'bz) && DIN[19]; // rv 0
  assign DIN_in[1] = (DIN[1] !== 1'bz) && DIN[1]; // rv 0
  assign DIN_in[20] = (DIN[20] !== 1'bz) && DIN[20]; // rv 0
  assign DIN_in[21] = (DIN[21] !== 1'bz) && DIN[21]; // rv 0
  assign DIN_in[22] = (DIN[22] !== 1'bz) && DIN[22]; // rv 0
  assign DIN_in[23] = (DIN[23] !== 1'bz) && DIN[23]; // rv 0
  assign DIN_in[24] = (DIN[24] !== 1'bz) && DIN[24]; // rv 0
  assign DIN_in[25] = (DIN[25] !== 1'bz) && DIN[25]; // rv 0
  assign DIN_in[26] = (DIN[26] !== 1'bz) && DIN[26]; // rv 0
  assign DIN_in[2] = (DIN[2] !== 1'bz) && DIN[2]; // rv 0
  assign DIN_in[3] = (DIN[3] !== 1'bz) && DIN[3]; // rv 0
  assign DIN_in[4] = (DIN[4] !== 1'bz) && DIN[4]; // rv 0
  assign DIN_in[5] = (DIN[5] !== 1'bz) && DIN[5]; // rv 0
  assign DIN_in[6] = (DIN[6] !== 1'bz) && DIN[6]; // rv 0
  assign DIN_in[7] = (DIN[7] !== 1'bz) && DIN[7]; // rv 0
  assign DIN_in[8] = (DIN[8] !== 1'bz) && DIN[8]; // rv 0
  assign DIN_in[9] = (DIN[9] !== 1'bz) && DIN[9]; // rv 0
  assign INMODE_in[0] = (INMODE[0] !== 1'bz) && (INMODE[0] ^ IS_INMODE_INVERTED_REG[0]); // rv 0
  assign INMODE_in[1] = (INMODE[1] !== 1'bz) && (INMODE[1] ^ IS_INMODE_INVERTED_REG[1]); // rv 0
  assign INMODE_in[2] = (INMODE[2] !== 1'bz) && (INMODE[2] ^ IS_INMODE_INVERTED_REG[2]); // rv 0
  assign INMODE_in[3] = (INMODE[3] !== 1'bz) && (INMODE[3] ^ IS_INMODE_INVERTED_REG[3]); // rv 0
  assign INMODE_in[4] = (INMODE[4] !== 1'bz) && (INMODE[4] ^ IS_INMODE_INVERTED_REG[4]); // rv 0
  assign RSTD_in = (RSTD !== 1'bz) && (RSTD ^ IS_RSTD_INVERTED_REG); // rv 0
  assign RSTINMODE_in = (RSTINMODE !== 1'bz) && (RSTINMODE ^ IS_RSTINMODE_INVERTED_REG); // rv 0


  assign A1_DATA_in = A1_DATA;
  assign A2_DATA_in = A2_DATA;
  assign B1_DATA_in = B1_DATA;
  assign B2_DATA_in = B2_DATA;


  reg attr_test;
  reg attr_err;

initial begin
  trig_attr = 1'b0;



  attr_test = 1'b0;

  attr_err = 1'b0;
  #1;
  trig_attr = ~trig_attr;
end































always @(trig_attr) begin
#1;
  ADREG_BIN = ADREG_REG[0];

  AMULTSEL_BIN =
    (AMULTSEL_REG == "A") ? AMULTSEL_A :
    (AMULTSEL_REG == "AD") ? AMULTSEL_AD :
     AMULTSEL_A;

  BMULTSEL_BIN =
    (BMULTSEL_REG == "B") ? BMULTSEL_B :
    (BMULTSEL_REG == "AD") ? BMULTSEL_AD :
     BMULTSEL_B;

  DREG_BIN = DREG_REG[0];

  INMODEREG_BIN = INMODEREG_REG[0];

  PREADDINSEL_BIN =
    (PREADDINSEL_REG == "A") ? PREADDINSEL_A :
    (PREADDINSEL_REG == "B") ? PREADDINSEL_B :
     PREADDINSEL_A;

  USE_MULT_BIN =
    (USE_MULT_REG == "MULTIPLY") ? USE_MULT_MULTIPLY :
    (USE_MULT_REG == "DYNAMIC") ? USE_MULT_DYNAMIC :
    (USE_MULT_REG == "NONE") ? USE_MULT_NONE :
     USE_MULT_MULTIPLY;

end



  initial begin
    $display("Error: [Unisim %s-100] SIMPRIM primitive is not intended for direct instantiation in RTL or functional netlists. This primitive is only available in the SIMPRIM library for implemented netlists, please ensure you are pointing to the correct library. Instance %m", MODULE_NAME);
    #1 $finish;
  end



  always @(trig_attr) begin
  #1;
    if ((attr_test == 1'b1) ||
        ((ADREG_REG != 1) &&
         (ADREG_REG != 0))) begin
      $display("Error: [Unisim %s-101] ADREG attribute is set to %d.  Legal values for this attribute are 1 or 0. Instance: %m", MODULE_NAME, ADREG_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((AMULTSEL_REG != "A") &&
         (AMULTSEL_REG != "AD"))) begin
      $display("Error: [Unisim %s-102] AMULTSEL attribute is set to %s.  Legal values for this attribute are A or AD. Instance: %m", MODULE_NAME, AMULTSEL_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((BMULTSEL_REG != "B") &&
         (BMULTSEL_REG != "AD"))) begin
      $display("Error: [Unisim %s-103] BMULTSEL attribute is set to %s.  Legal values for this attribute are B or AD. Instance: %m", MODULE_NAME, BMULTSEL_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((DREG_REG != 1) &&
         (DREG_REG != 0))) begin
      $display("Error: [Unisim %s-104] DREG attribute is set to %d.  Legal values for this attribute are 1 or 0. Instance: %m", MODULE_NAME, DREG_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((INMODEREG_REG != 1) &&
         (INMODEREG_REG != 0))) begin
      $display("Error: [Unisim %s-105] INMODEREG attribute is set to %d.  Legal values for this attribute are 1 or 0. Instance: %m", MODULE_NAME, INMODEREG_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((PREADDINSEL_REG != "A") &&
         (PREADDINSEL_REG != "B"))) begin
      $display("Error: [Unisim %s-110] PREADDINSEL attribute is set to %s.  Legal values for this attribute are A or B. Instance: %m", MODULE_NAME, PREADDINSEL_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((USE_MULT_REG != "MULTIPLY") &&
         (USE_MULT_REG != "DYNAMIC") &&
         (USE_MULT_REG != "NONE"))) begin
      $display("Error: [Unisim %s-111] USE_MULT attribute is set to %s.  Legal values for this attribute are MULTIPLY, DYNAMIC or NONE. Instance: %m", MODULE_NAME, USE_MULT_REG);
      attr_err = 1'b1;
    end

    if (attr_err == 1'b1) #1 $finish;
  end






// begin behavioral model

  localparam D_WIDTH   = 27;
  wire [26:0] a1a2_i_mux;
  wire [17:0] b1b2_i_mux;
  wire [4:0] INMODE_mux;
  reg [4:0]  INMODE_reg;
  reg [D_WIDTH-1:0] AD_DATA_reg;
  reg [D_WIDTH-1:0] D_DATA_reg;

  reg DREG_INT;
  reg ADREG_INT;

// initialize regs

initial begin
  INMODE_reg = 5'b0;
  AD_DATA_reg = {D_WIDTH{1'b0}};
  D_DATA_reg = {D_WIDTH{1'b0}};
end


  always @ (*) begin
    if (((AMULTSEL_BIN == AMULTSEL_A) &&
         (BMULTSEL_BIN == BMULTSEL_B)) ||
        (USE_MULT_BIN == USE_MULT_NONE)) begin
      DREG_INT = 1'b0;
    end else begin
      DREG_INT = DREG_BIN;
    end
  end

  always @ (*) begin
    if (((AMULTSEL_BIN == AMULTSEL_A) && (BMULTSEL_BIN == BMULTSEL_B)) ||
        (USE_MULT_BIN == USE_MULT_NONE)) begin
      ADREG_INT = 1'b0;
    end else begin
      ADREG_INT = ADREG_BIN;
    end
  end

   assign a1a2_i_mux = INMODE_mux[0] ? A1_DATA_in : A2_DATA_in;
   assign b1b2_i_mux = INMODE_mux[4] ? B1_DATA_in : B2_DATA_in;
   assign A2A1      = ((PREADDINSEL_BIN==PREADDINSEL_A) && INMODE_mux[1]) ? 27'b0 : a1a2_i_mux;
   assign B2B1      = ((PREADDINSEL_BIN==PREADDINSEL_B) && INMODE_mux[1]) ? 18'b0 : b1b2_i_mux;
   assign ADDSUB   = INMODE_mux[3];

   assign INMODE_2 = INMODE_mux[2];

   assign PREADD_AB    = (PREADDINSEL_BIN==PREADDINSEL_B) ? {{9{B2B1[17]}}, B2B1} : A2A1;

//*********************************************************
//**********  INMODE signal registering        ************
//*********************************************************
// new 

   always @(posedge CLK_in) begin
      if (RSTINMODE_in || (INMODEREG_BIN == 1'b0) || glblGSR) begin
         INMODE_reg <= 5'b0;
      end else if (CEINMODE_in) begin
         INMODE_reg <= INMODE_in;
      end
   end

   assign INMODE_mux = (INMODEREG_BIN == 1'b1) ? INMODE_reg : INMODE_in;

//*********************************************************
//*** Input register D with 1 level deep of register
//*********************************************************

   always @(posedge CLK_in) begin
      if (RSTD_in || (DREG_INT == 1'b0) || glblGSR) begin
         D_DATA_reg <= {D_WIDTH{1'b0}};
      end else if (CED_in) begin
         D_DATA_reg <= DIN_in;
      end
   end

   assign D_DATA    = (DREG_INT == 1'b1) ? D_DATA_reg : DIN_in;

//*********************************************************
//*** Input register AD with 1 level deep of register
//*********************************************************

   always @(posedge CLK_in) begin
      if      (RSTD_in || glblGSR)  begin
         AD_DATA_reg <= 27'b0;
      end else if (CEAD_in) AD_DATA_reg <= AD_in;
   end

   assign AD_DATA    = (ADREG_INT == 1'b1) ? AD_DATA_reg : AD_in;

// end behavioral model










  specify
    (A1_DATA *> A2A1) = (0:0:0, 0:0:0);
    (A1_DATA *> PREADD_AB) = (0:0:0, 0:0:0);
    (A2_DATA *> A2A1) = (0:0:0, 0:0:0);
    (A2_DATA *> PREADD_AB) = (0:0:0, 0:0:0);
    (AD *> AD_DATA) = (0:0:0, 0:0:0);
    (B1_DATA *> B2B1) = (0:0:0, 0:0:0);
    (B1_DATA *> PREADD_AB) = (0:0:0, 0:0:0);
    (B2_DATA *> B2B1) = (0:0:0, 0:0:0);
    (B2_DATA *> PREADD_AB) = (0:0:0, 0:0:0);
    (CLK *> A2A1) = (0:0:0, 0:0:0);
    (CLK *> AD_DATA) = (0:0:0, 0:0:0);
    (CLK *> B2B1) = (0:0:0, 0:0:0);
    (CLK *> D_DATA) = (0:0:0, 0:0:0);
    (CLK *> PREADD_AB) = (0:0:0, 0:0:0);
    (CLK => ADDSUB) = (0:0:0, 0:0:0);
    (CLK => INMODE_2) = (0:0:0, 0:0:0);
    (DIN *> D_DATA) = (0:0:0, 0:0:0);
    (INMODE *> A2A1) = (0:0:0, 0:0:0);
    (INMODE *> ADDSUB) = (0:0:0, 0:0:0);
    (INMODE *> B2B1) = (0:0:0, 0:0:0);
    (INMODE *> INMODE_2) = (0:0:0, 0:0:0);
    (INMODE *> PREADD_AB) = (0:0:0, 0:0:0);


































    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
