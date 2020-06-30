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
//  /   /                        DSP_A_B_DATA
// /___/   /\      Filename    : DSP_A_B_DATA.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//  07/15/12 - Migrate from E1.
//  12/10/12 - Add dynamic registers
//  03/06/13 - 701316 - A_B_reg no clk when REG=0
//  04/08/13 - 710304 - AREG, BREG, ACASCREG and BCASCREG dynamic registers mis sized.
//  04/22/13 - 714213 - ACOUT, BCOUT wrong logic
//  04/23/13 - 714772 - remove sensitivity to negedge GSR
//  05/07/13 - 716896 - AREG, BREG, ACASCREG and BCASCREG localparams mis sized.
//  10/22/14 - 808642 - Added #1 to $finish
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps


`celldefine


module DSP_A_B_DATA #(



  parameter integer ACASCREG = 1,
  parameter integer AREG = 1,
  parameter A_INPUT = "DIRECT",
  parameter integer BCASCREG = 1,
  parameter integer BREG = 1,
  parameter B_INPUT = "DIRECT",
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [0:0] IS_RSTA_INVERTED = 1'b0,
  parameter [0:0] IS_RSTB_INVERTED = 1'b0
)(
  output [26:0] A1_DATA,
  output [26:0] A2_DATA,
  output [29:0] ACOUT,
  output [29:0] A_ALU,
  output [17:0] B1_DATA,
  output [17:0] B2_DATA,
  output [17:0] BCOUT,
  output [17:0] B_ALU,

  input [29:0] A,
  input [29:0] ACIN,
  input [17:0] B,
  input [17:0] BCIN,
  input CEA1,
  input CEA2,
  input CEB1,
  input CEB2,
  input CLK,
  input RSTA,
  input RSTB
);
  
// define constants
  localparam MODULE_NAME = "DSP_A_B_DATA";

// Parameter encodings and registers
  localparam A_INPUT_CASCADE = 1;
  localparam A_INPUT_DIRECT = 0;
  localparam B_INPUT_CASCADE = 1;
  localparam B_INPUT_DIRECT = 0;

  reg trig_attr;
// include dynamic registers - XILINX test only



  reg [31:0] ACASCREG_REG = ACASCREG;
  reg [31:0] AREG_REG = AREG;
  reg [56:1] A_INPUT_REG = A_INPUT;
  reg [31:0] BCASCREG_REG = BCASCREG;
  reg [31:0] BREG_REG = BREG;
  reg [56:1] B_INPUT_REG = B_INPUT;
  reg [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
  reg [0:0] IS_RSTA_INVERTED_REG = IS_RSTA_INVERTED;
  reg [0:0] IS_RSTB_INVERTED_REG = IS_RSTB_INVERTED;










  reg [1:0] ACASCREG_BIN;
  reg [1:0] AREG_BIN;
  reg A_INPUT_BIN;
  reg [1:0] BCASCREG_BIN;
  reg [1:0] BREG_BIN;
  reg B_INPUT_BIN;





  tri0 glblGSR = glbl.GSR;


  wire CEA1_in;
  wire CEA2_in;
  wire CEB1_in;
  wire CEB2_in;
  wire CLK_in;
  wire RSTA_in;
  wire RSTB_in;
  wire [17:0] BCIN_in;
  wire [17:0] B_in;
  wire [29:0] ACIN_in;
  wire [29:0] A_in;














  




  assign ACIN_in = ACIN;
  assign A_in[0] = (A[0] === 1'bz) || A[0]; // rv 1
  assign A_in[10] = (A[10] === 1'bz) || A[10]; // rv 1
  assign A_in[11] = (A[11] === 1'bz) || A[11]; // rv 1
  assign A_in[12] = (A[12] === 1'bz) || A[12]; // rv 1
  assign A_in[13] = (A[13] === 1'bz) || A[13]; // rv 1
  assign A_in[14] = (A[14] === 1'bz) || A[14]; // rv 1
  assign A_in[15] = (A[15] === 1'bz) || A[15]; // rv 1
  assign A_in[16] = (A[16] === 1'bz) || A[16]; // rv 1
  assign A_in[17] = (A[17] === 1'bz) || A[17]; // rv 1
  assign A_in[18] = (A[18] === 1'bz) || A[18]; // rv 1
  assign A_in[19] = (A[19] === 1'bz) || A[19]; // rv 1
  assign A_in[1] = (A[1] === 1'bz) || A[1]; // rv 1
  assign A_in[20] = (A[20] === 1'bz) || A[20]; // rv 1
  assign A_in[21] = (A[21] === 1'bz) || A[21]; // rv 1
  assign A_in[22] = (A[22] === 1'bz) || A[22]; // rv 1
  assign A_in[23] = (A[23] === 1'bz) || A[23]; // rv 1
  assign A_in[24] = (A[24] === 1'bz) || A[24]; // rv 1
  assign A_in[25] = (A[25] === 1'bz) || A[25]; // rv 1
  assign A_in[26] = (A[26] === 1'bz) || A[26]; // rv 1
  assign A_in[27] = (A[27] === 1'bz) || A[27]; // rv 1
  assign A_in[28] = (A[28] === 1'bz) || A[28]; // rv 1
  assign A_in[29] = (A[29] === 1'bz) || A[29]; // rv 1
  assign A_in[2] = (A[2] === 1'bz) || A[2]; // rv 1
  assign A_in[3] = (A[3] === 1'bz) || A[3]; // rv 1
  assign A_in[4] = (A[4] === 1'bz) || A[4]; // rv 1
  assign A_in[5] = (A[5] === 1'bz) || A[5]; // rv 1
  assign A_in[6] = (A[6] === 1'bz) || A[6]; // rv 1
  assign A_in[7] = (A[7] === 1'bz) || A[7]; // rv 1
  assign A_in[8] = (A[8] === 1'bz) || A[8]; // rv 1
  assign A_in[9] = (A[9] === 1'bz) || A[9]; // rv 1
  assign BCIN_in = BCIN;
  assign B_in[0] = (B[0] === 1'bz) || B[0]; // rv 1
  assign B_in[10] = (B[10] === 1'bz) || B[10]; // rv 1
  assign B_in[11] = (B[11] === 1'bz) || B[11]; // rv 1
  assign B_in[12] = (B[12] === 1'bz) || B[12]; // rv 1
  assign B_in[13] = (B[13] === 1'bz) || B[13]; // rv 1
  assign B_in[14] = (B[14] === 1'bz) || B[14]; // rv 1
  assign B_in[15] = (B[15] === 1'bz) || B[15]; // rv 1
  assign B_in[16] = (B[16] === 1'bz) || B[16]; // rv 1
  assign B_in[17] = (B[17] === 1'bz) || B[17]; // rv 1
  assign B_in[1] = (B[1] === 1'bz) || B[1]; // rv 1
  assign B_in[2] = (B[2] === 1'bz) || B[2]; // rv 1
  assign B_in[3] = (B[3] === 1'bz) || B[3]; // rv 1
  assign B_in[4] = (B[4] === 1'bz) || B[4]; // rv 1
  assign B_in[5] = (B[5] === 1'bz) || B[5]; // rv 1
  assign B_in[6] = (B[6] === 1'bz) || B[6]; // rv 1
  assign B_in[7] = (B[7] === 1'bz) || B[7]; // rv 1
  assign B_in[8] = (B[8] === 1'bz) || B[8]; // rv 1
  assign B_in[9] = (B[9] === 1'bz) || B[9]; // rv 1
  assign CEA1_in = (CEA1 !== 1'bz) && CEA1; // rv 0
  assign CEA2_in = (CEA2 !== 1'bz) && CEA2; // rv 0
  assign CEB1_in = (CEB1 !== 1'bz) && CEB1; // rv 0
  assign CEB2_in = (CEB2 !== 1'bz) && CEB2; // rv 0
  assign CLK_in = (CLK !== 1'bz) && (CLK ^ IS_CLK_INVERTED_REG); // rv 0
  assign RSTA_in = (RSTA !== 1'bz) && (RSTA ^ IS_RSTA_INVERTED_REG); // rv 0
  assign RSTB_in = (RSTB !== 1'bz) && (RSTB ^ IS_RSTB_INVERTED_REG); // rv 0



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
  ACASCREG_BIN = ACASCREG_REG[1:0];

  AREG_BIN = AREG_REG[1:0];

  A_INPUT_BIN =
    (A_INPUT_REG == "DIRECT") ? A_INPUT_DIRECT :
    (A_INPUT_REG == "CASCADE") ? A_INPUT_CASCADE :
     A_INPUT_DIRECT;

  BCASCREG_BIN = BCASCREG_REG[1:0];

  BREG_BIN = BREG_REG[1:0];

  B_INPUT_BIN =
    (B_INPUT_REG == "DIRECT") ? B_INPUT_DIRECT :
    (B_INPUT_REG == "CASCADE") ? B_INPUT_CASCADE :
     B_INPUT_DIRECT;

end



  initial begin
    $display("Error: [Unisim %s-100] SIMPRIM primitive is not intended for direct instantiation in RTL or functional netlists. This primitive is only available in the SIMPRIM library for implemented netlists, please ensure you are pointing to the correct library. Instance %m", MODULE_NAME);
    #1 $finish;
  end



  always @(trig_attr) begin
  #1;
    if ((attr_test == 1'b1) ||
        ((ACASCREG_REG != 1) &&
         (ACASCREG_REG != 0) &&
         (ACASCREG_REG != 2))) begin
      $display("Error: [Unisim %s-101] ACASCREG attribute is set to %d.  Legal values for this attribute are 1, 0 or 2. Instance: %m", MODULE_NAME, ACASCREG_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((AREG_REG != 1) &&
         (AREG_REG != 0) &&
         (AREG_REG != 2))) begin
      $display("Error: [Unisim %s-102] AREG attribute is set to %d.  Legal values for this attribute are 1, 0 or 2. Instance: %m", MODULE_NAME, AREG_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((A_INPUT_REG != "DIRECT") &&
         (A_INPUT_REG != "CASCADE"))) begin
      $display("Error: [Unisim %s-103] A_INPUT attribute is set to %s.  Legal values for this attribute are DIRECT or CASCADE. Instance: %m", MODULE_NAME, A_INPUT_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((BCASCREG_REG != 1) &&
         (BCASCREG_REG != 0) &&
         (BCASCREG_REG != 2))) begin
      $display("Error: [Unisim %s-104] BCASCREG attribute is set to %d.  Legal values for this attribute are 1, 0 or 2. Instance: %m", MODULE_NAME, BCASCREG_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((BREG_REG != 1) &&
         (BREG_REG != 0) &&
         (BREG_REG != 2))) begin
      $display("Error: [Unisim %s-105] BREG attribute is set to %d.  Legal values for this attribute are 1, 0 or 2. Instance: %m", MODULE_NAME, BREG_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((B_INPUT_REG != "DIRECT") &&
         (B_INPUT_REG != "CASCADE"))) begin
      $display("Error: [Unisim %s-106] B_INPUT attribute is set to %s.  Legal values for this attribute are DIRECT or CASCADE. Instance: %m", MODULE_NAME, B_INPUT_REG);
      attr_err = 1'b1;
    end

    if (attr_err == 1'b1) #1 $finish;
  end






// begin behavioral model

  always @(trig_attr) begin
    #1;
    case (AREG_REG)
      0, 1 : if (AREG_REG != ACASCREG_REG) begin
      $display("Error: [Unisim %s-2] AREG attribute is set to %0d and ACASCREG attribute is set to %0d. When AREG is 0 or 1, ACASCREG must be set to the same value. Instance: %m", MODULE_NAME, AREG_REG, ACASCREG_REG);
        attr_err = 1'b1;
        end
      2 : if (ACASCREG_REG == 0) begin
      $display("Error: [Unisim %s-3] AREG attribute is set to %0d and ACASCREG attribute is set to %0d. When AREG is 2, ACASCREG must be set to 1 or 2. Instance: %m", MODULE_NAME, AREG_REG, ACASCREG_REG);
        attr_err = 1'b1;
        end
    endcase

    case (BREG_REG)
      0, 1 : if (BREG_REG != BCASCREG_REG) begin
      $display("Error: [Unisim %s-4] BREG attribute is set to %0d and BCASCREG attribute is set to %0d. When BREG is 0 or 1, BCASCREG must be set to the same value. Instance: %m", MODULE_NAME, BREG_REG, BCASCREG_REG);
        attr_err = 1'b1;
        end
      2 : if (BCASCREG_REG == 0) begin
      $display("Error: [Unisim %s-5] BREG attribute is set to %0d and BCASCREG attribute is set to %0d. When BREG is 2, BCASCREG must be set to 1 or 2. Instance: %m", MODULE_NAME, BREG_REG, BCASCREG_REG);
        attr_err = 1'b1;
        end
    endcase

    if (attr_err == 1'b1) #1 $finish;
  end

  localparam A_WIDTH   = 30;
  localparam B_WIDTH   = 18;
  reg [29:0] A1_reg;
  reg [29:0] A2_reg;
  wire [17:0] B_BCIN_mux;
  reg [17:0] B2_reg;
  reg [B_WIDTH-1:0] B1_DATA_out;

// initialize regs

initial begin
  A1_reg = 30'b0;
  A2_reg = 30'b0;
  B2_reg = 18'b0;
  B1_DATA_out = {B_WIDTH{1'b0}};
end


//*********************************************************
//*** Input register A with 2 level deep of registers
//*********************************************************

    always @(posedge CLK_in) begin
       if (RSTA_in || (AREG_BIN == 2'b00) || glblGSR) begin
          A1_reg <= {A_WIDTH{1'b0}};
       end else if (CEA1_in) begin
          if (A_INPUT_BIN == A_INPUT_CASCADE) begin
             A1_reg <= ACIN_in;
          end else begin
             A1_reg <= A_in;
          end
       end
    end

    always @(posedge CLK_in) begin
       if (RSTA_in || (AREG_BIN == 2'b00) || glblGSR) begin
          A2_reg <= {A_WIDTH{1'b0}};
       end else if (CEA2_in) begin
          if (AREG_BIN == 2'b10) begin
             A2_reg <= A1_reg;
          end else if (A_INPUT_BIN == A_INPUT_CASCADE) begin
             A2_reg <= ACIN_in;
          end else begin
             A2_reg <= A_in;
          end
       end
    end

    assign A_ALU = (AREG_BIN != 2'b00) ? A2_reg :
                   (A_INPUT_BIN == A_INPUT_CASCADE) ? ACIN_in :
                   A_in;

// assumes encoding the same for ACASCREG and AREG
    assign ACOUT = (ACASCREG_BIN == AREG_BIN) ? A_ALU : A1_reg;
    assign A1_DATA = A1_reg[26:0];

    assign A2_DATA = A_ALU[26:0];

    assign B1_DATA = B1_DATA_out;


//*********************************************************
//*** Input register B with 2 level deep of registers
//*********************************************************

    always @(posedge CLK_in) begin
       if (RSTB_in || (BREG_BIN == 2'b00) || glblGSR) begin
          B1_DATA_out <= 18'b0;
       end else if (CEB1_in) begin
          if (B_INPUT_BIN == B_INPUT_CASCADE) B1_DATA_out <= BCIN_in;
          else B1_DATA_out <= B_in;
       end
    end

    always @(posedge CLK_in) begin
       if (RSTB_in || glblGSR) B2_reg <= 18'b0;
       else if (CEB2_in) begin
         if (BREG_BIN == 2'b10) B2_reg <= B1_DATA_out;
         else if (B_INPUT_BIN == B_INPUT_CASCADE) B2_reg <= BCIN_in;
         else B2_reg <= B_in;
       end
    end

    assign B_ALU = (BREG_BIN != 2'b00) ? B2_reg :
                   (B_INPUT_BIN == B_INPUT_CASCADE) ?  BCIN_in :
                    B_in;

    assign B2_DATA = (BREG_BIN != 2'b00) ? B2_reg :
                     (B_INPUT_BIN == B_INPUT_CASCADE) ?  BCIN_in :
                      B_in;

// assumes encoding the same for BCASCREG and BREG
    assign BCOUT = (BCASCREG_BIN == BREG_BIN) ? B2_DATA : B1_DATA_out;

// end behavioral model










  specify
    (A *> A2_DATA) = (0:0:0, 0:0:0);
    (A *> ACOUT) = (0:0:0, 0:0:0);
    (A *> A_ALU) = (0:0:0, 0:0:0);
    (ACIN *> A2_DATA) = (0:0:0, 0:0:0);
    (ACIN *> ACOUT) = (0:0:0, 0:0:0);
    (ACIN *> A_ALU) = (0:0:0, 0:0:0);
    (B *> B2_DATA) = (0:0:0, 0:0:0);
    (B *> BCOUT) = (0:0:0, 0:0:0);
    (B *> B_ALU) = (0:0:0, 0:0:0);
    (BCIN *> B2_DATA) = (0:0:0, 0:0:0);
    (BCIN *> BCOUT) = (0:0:0, 0:0:0);
    (BCIN *> B_ALU) = (0:0:0, 0:0:0);
    (CLK *> A1_DATA) = (0:0:0, 0:0:0);
    (CLK *> A2_DATA) = (0:0:0, 0:0:0);
    (CLK *> ACOUT) = (0:0:0, 0:0:0);
    (CLK *> A_ALU) = (0:0:0, 0:0:0);
    (CLK *> B1_DATA) = (0:0:0, 0:0:0);
    (CLK *> B2_DATA) = (0:0:0, 0:0:0);
    (CLK *> BCOUT) = (0:0:0, 0:0:0);
    (CLK *> B_ALU) = (0:0:0, 0:0:0);












































    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine

