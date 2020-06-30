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
// \   \   \/      Version     : 2016.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        18X18 Signed Multiplier Followed by Three-Input Adder plus ALU with Pipeline Registers
// /___/   /\     Filename     : DSP48E1.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision:
//    05/21/09 - Initial version.
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//    07/24/13 - add optinv
//    10/22/14 - Added #1 to $finish (CR 808642).
// End Revision
///////////////////////////////////////////////////////////////////////////////

`timescale  1 ps / 1 ps

`celldefine

module DSP48E1 #(
  `ifdef XIL_TIMING
  parameter LOC = "UNPLACED",  
  `endif
  parameter integer ACASCREG = 1,
  parameter integer ADREG = 1,
  parameter integer ALUMODEREG = 1,
  parameter integer AREG = 1,
  parameter AUTORESET_PATDET = "NO_RESET",
  parameter A_INPUT = "DIRECT",
  parameter integer BCASCREG = 1,
  parameter integer BREG = 1,
  parameter B_INPUT = "DIRECT",
  parameter integer CARRYINREG = 1,
  parameter integer CARRYINSELREG = 1,
  parameter integer CREG = 1,
  parameter integer DREG = 1,
  parameter integer INMODEREG = 1,
  parameter [3:0] IS_ALUMODE_INVERTED = 4'b0000,
  parameter [0:0] IS_CARRYIN_INVERTED = 1'b0,
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [4:0] IS_INMODE_INVERTED = 5'b00000,
  parameter [6:0] IS_OPMODE_INVERTED = 7'b0000000,
  parameter [47:0] MASK = 48'h3FFFFFFFFFFF,
  parameter integer MREG = 1,
  parameter integer OPMODEREG = 1,
  parameter [47:0] PATTERN = 48'h000000000000,
  parameter integer PREG = 1,
  parameter SEL_MASK = "MASK",
  parameter SEL_PATTERN = "PATTERN",
  parameter USE_DPORT = "FALSE",
  parameter USE_MULT = "MULTIPLY",
  parameter USE_PATTERN_DETECT = "NO_PATDET",
  parameter USE_SIMD = "ONE48"
)(
  output [29:0] ACOUT,
  output [17:0] BCOUT,
  output CARRYCASCOUT,
  output [3:0] CARRYOUT,
  output MULTSIGNOUT,
  output OVERFLOW,
  output [47:0] P,
  output PATTERNBDETECT,
  output PATTERNDETECT,
  output [47:0] PCOUT,
  output UNDERFLOW,

  input [29:0] A,
  input [29:0] ACIN,
  input [3:0] ALUMODE,
  input [17:0] B,
  input [17:0] BCIN,
  input [47:0] C,
  input CARRYCASCIN,
  input CARRYIN,
  input [2:0] CARRYINSEL,
  input CEA1,
  input CEA2,
  input CEAD,
  input CEALUMODE,
  input CEB1,
  input CEB2,
  input CEC,
  input CECARRYIN,
  input CECTRL,
  input CED,
  input CEINMODE,
  input CEM,
  input CEP,
  input CLK,
  input [24:0] D,
  input [4:0] INMODE,
  input MULTSIGNIN,
  input [6:0] OPMODE,
  input [47:0] PCIN,
  input RSTA,
  input RSTALLCARRYIN,
  input RSTALUMODE,
  input RSTB,
  input RSTC,
  input RSTCTRL,
  input RSTD,
  input RSTINMODE,
  input RSTM,
  input RSTP
);
  
// define constants
   localparam MODULE_NAME = "DSP48E1";

   tri0  GSR = glbl.GSR;

//------------------- constants -------------------------
   localparam MAX_ACOUT      = 30;
   localparam MAX_BCOUT      = 18;
   localparam MAX_CARRYOUT   = 4;
   localparam MAX_P          = 48;
   localparam MAX_PCOUT      = 48;

   localparam MAX_A          = 30;
   localparam MAX_ACIN       = 30;
   localparam MAX_ALUMODE    = 4;
   localparam MAX_A_MULT     = 25;
   localparam MAX_B          = 18;
   localparam MAX_B_MULT     = 18;
   localparam MAX_BCIN       = 18;
   localparam MAX_C          = 48;
   localparam MAX_CARRYINSEL = 3;
   localparam MAX_D          = 25;
   localparam MAX_INMODE     = 5;
   localparam MAX_OPMODE     = 7;
   localparam MAX_PCIN       = 48;

   localparam MAX_ALU_FULL   = 48;
   localparam MAX_ALU_HALF   = 24;
   localparam MAX_ALU_QUART  = 12;

   localparam MSB_ACOUT      = MAX_ACOUT - 1;
   localparam MSB_BCOUT      = MAX_BCOUT - 1;
   localparam MSB_CARRYOUT   = MAX_CARRYOUT - 1;
   localparam MSB_P          = MAX_P - 1;
   localparam MSB_PCOUT      = MAX_PCOUT - 1;
 
   localparam MSB_A          = MAX_A - 1;
   localparam MSB_ACIN       = MAX_ACIN - 1;
   localparam MSB_ALUMODE    = MAX_ALUMODE - 1;
   localparam MSB_A_MULT     = MAX_A_MULT - 1;
   localparam MSB_B          = MAX_B - 1;
   localparam MSB_B_MULT     = MAX_B_MULT - 1;
   localparam MSB_BCIN       = MAX_BCIN - 1;
   localparam MSB_C          = MAX_C - 1;
   localparam MSB_CARRYINSEL = MAX_CARRYINSEL - 1;
   localparam MSB_D          = MAX_D - 1;
   localparam MSB_INMODE     = MAX_INMODE - 1;
   localparam MSB_OPMODE     = MAX_OPMODE - 1;
   localparam MSB_PCIN       = MAX_PCIN - 1;

   localparam MSB_ALU_FULL   = MAX_ALU_FULL  - 1;
   localparam MSB_ALU_HALF   = MAX_ALU_HALF  - 1;
   localparam MSB_ALU_QUART  = MAX_ALU_QUART - 1;

   localparam SHIFT_MUXZ     = 17;

  wire [3:0] IS_ALUMODE_INVERTED_BIN = IS_ALUMODE_INVERTED;
  wire [0:0] IS_CARRYIN_INVERTED_BIN = IS_CARRYIN_INVERTED;
  wire [0:0] IS_CLK_INVERTED_BIN = IS_CLK_INVERTED;
  wire [4:0] IS_INMODE_INVERTED_BIN = IS_INMODE_INVERTED;
  wire [6:0] IS_OPMODE_INVERTED_BIN = IS_OPMODE_INVERTED;

    reg [29:0] a_o_mux, qa_o_mux, qa_o_reg1, qa_o_reg2, qacout_o_mux;

// new
    reg [4:0]  qinmode_o_mux, qinmode_o_reg;
// new
    wire [24:0] a_preaddsub;

    reg [17:0] b_o_mux, qb_o_mux, qb_o_reg1, qb_o_reg2, qbcout_o_mux;
    reg [2:0] qcarryinsel_o_mux, qcarryinsel_o_reg1;

// new  
    reg [MSB_D:0] d_o_mux, qd_o_mux, qd_o_reg1;

    reg [(MSB_A_MULT+MSB_B_MULT+1):0] qmult_o_mux, qmult_o_reg; // 42:0
    reg [47:0] qc_o_mux, qc_o_reg1;
    reg [47:0] qp_o_mux, qp_o_reg1;
    reg [47:0] qx_o_mux, qy_o_mux, qz_o_mux;
    reg [6:0]  qopmode_o_mux, qopmode_o_reg1;

    reg notifier;

    reg qcarryin_o_mux0, qcarryin_o_reg0, qcarryin_o_mux7, qcarryin_o_reg7;
    reg qcarryin_o_mux, qcarryin_o_reg;

    reg [3:0]  qalumode_o_mux, qalumode_o_reg1;

    reg invalid_opmode, opmode_valid_flag, ping_opmode_drc_check = 0;

//    reg [47:0] alu_o;
    wire [47:0] alu_o;

    reg qmultsignout_o_reg, multsignout_o_mux; 
    wire multsignout_o_opmode;

    reg [MAX_ALU_FULL:0]  alu_full_tmp;
    reg [MAX_ALU_HALF:0]  alu_hlf1_tmp, alu_hlf2_tmp;
    reg [MAX_ALU_QUART:0] alu_qrt1_tmp,  alu_qrt2_tmp, alu_qrt3_tmp, alu_qrt4_tmp;
    
    wire pdet_o_mux, pdetb_o_mux;

    wire [47:0] the_pattern; 
    reg [47:0] the_mask = 0;
    wire carrycascout_o;
    wire the_auto_reset_patdet;
    reg carrycascout_o_reg = 0;
    reg carrycascout_o_mux = 0;

//    reg [3:0] carryout_o = 0;
//  CR 577648
//    reg [3:0] carryout_o_reg = 0;
//    reg [3:0] carryout_o_mux = 0;
//  CR 588861
    reg [3:0] carryout_o_reg = 0;
    reg [3:0] carryout_o_mux;
    wire [3:0] carryout_x_o;

    wire pdet_o, pdetb_o;
    reg  pdet_o_reg1, pdet_o_reg2, pdetb_o_reg1, pdetb_o_reg2;
    wire overflow_o, underflow_o;

    wire [(MSB_A_MULT+MSB_B_MULT+1):0] mult_o;
//    reg [(MSB_A_MULT+MSB_B_MULT+1):0] mult_o;  // 42:0
// new 
    wire [MSB_A_MULT:0] ad_addsub, ad_mult;
    reg  [MSB_A_MULT:0] qad_o_reg1, qad_o_mux;
    wire [MSB_B_MULT:0] b_mult;

    reg cci_drc_msg = 1'b0;
    reg cis_drc_msg = 1'b0;

    wire [MSB_A:0] a_in;
    wire [MSB_ACIN:0] acin_in;
    wire [MSB_B:0] b_in;
    wire [MSB_BCIN:0] bcin_in;
    wire [MSB_CARRYINSEL:0] carryinsel_in;
    wire [MSB_PCIN:0] pcin_in, c_in;
    wire [MSB_OPMODE:0] opmode_in;
    wire [MSB_ALUMODE:0] alumode_in;
    wire carryin_in;
    wire carrycascin_in;
    wire cep_in;
    wire cea1_in;
    wire cea2_in;
    wire cealumode_in;
    wire ceb1_in;
    wire ceb2_in;
    wire cec_in;
    wire cead_in;
    wire ced_in;
    wire cecarryin_in;
    wire cectrl_in;
    wire ceinmode_in;
    wire cem_in;
    wire clk_in;
    wire [MSB_D:0] d_in;
    wire gsr_in;
    wire [MSB_INMODE:0] inmode_in;
    wire multsignin_in;
    wire rstp_in;
    wire rsta_in;
    wire rstalumode_in;
    wire rstb_in;
    wire rstallcarryin_in;
    wire rstc_in;
    wire rstctrl_in;
    wire rstd_in;
    wire rstinmode_in;
    wire rstm_in;

    wire [MSB_A:0] a_dly;
    wire [MSB_ACIN:0] acin_dly;
    wire [MSB_B:0] b_dly;
    wire [MSB_BCIN:0] bcin_dly;
    wire [MSB_CARRYINSEL:0] carryinsel_dly;
    wire [MSB_PCIN:0] pcin_dly, c_dly;
    wire [MSB_OPMODE:0] opmode_dly;
    wire [MSB_ALUMODE:0] alumode_dly;
    wire carryin_dly;
    wire carrycascin_dly;
    wire cep_dly;
    wire cea1_dly;
    wire cea2_dly;
    wire cealumode_dly;
    wire ceb1_dly;
    wire ceb2_dly;
    wire cec_dly;
    wire cead_dly;
    wire ced_dly;
    wire cecarryin_dly;
    wire cectrl_dly;
    wire ceinmode_dly;
    wire cem_dly;
    wire clk_dly;
    wire [MSB_D:0] d_dly;
    wire [MSB_INMODE:0] inmode_dly;
    wire multsignin_dly;
    wire rstp_dly;
    wire rsta_dly;
    wire rstalumode_dly;
    wire rstb_dly;
    wire rstallcarryin_dly;
    wire rstc_dly;
    wire rstctrl_dly;
    wire rstd_dly;
    wire rstinmode_dly;
    wire rstm_dly;

`ifdef XIL_TIMING
//    wire nrsta;
//    wire nrstb;
//    wire nrstc;
//    wire nrstp;
//    wire nrstallcarryin;
//    wire nrstctrl;
    wire cea12_enable;
    wire ceb12_enable;
    wire a_en_n, a_en_p;
    wire b_en_n, b_en_p;
    wire c_en_n, c_en_p;
    wire d_en_n, d_en_p;
    wire acin_en_n, acin_en_p;
    wire bcin_en_n, bcin_en_p;
    wire carryin_en_n, carryin_en_p;
    wire carryinsel_en_n, carryinsel_en_p;
    wire opmode_en_n, opmode_en_p;
    wire inmode_en_n, inmode_en_p;
    wire pcin_en_n, pcin_en_p;
    wire clk_en_n, clk_en_p;
    wire clk_gsr_en_n, clk_gsr_en_p;
    wire clk_rsta_en_n, clk_rsta_en_p;
    wire clk_rstb_en_n, clk_rstb_en_p;
    wire clk_rstc_en_n, clk_rstc_en_p;
    wire clk_rstd_en_n, clk_rstd_en_p;
    wire clk_rstm_en_n, clk_rstm_en_p;
    wire clk_rstp_en_n, clk_rstp_en_p;
    wire clk_rstallcarryin_en_n, clk_rstallcarryin_en_p;
    wire clk_rstctrl_en_n, clk_rstctrl_en_p;
    wire clk_rstinmode_en_n, clk_rstinmode_en_p;
`endif

//----------------------------------------------------------------------
//------------------------  Output Ports  ------------------------------
//----------------------------------------------------------------------
    buf b_acout_o[MSB_ACOUT:0] (ACOUT, qacout_o_mux);
    buf b_bcout_o[MSB_BCOUT:0] (BCOUT, qbcout_o_mux);
    buf b_carrycascout (CARRYCASCOUT, carrycascout_o_mux);
    buf b_carryout[MSB_CARRYOUT:0] (CARRYOUT, carryout_x_o);
    buf b_multsignout (MULTSIGNOUT,  multsignout_o_mux);
    buf b_overflow (OVERFLOW,  overflow_o);
    buf b_p_o[MSB_P:0] (P, qp_o_mux);
    buf b_pcout_o[MSB_PCOUT:0] (PCOUT, qp_o_mux);
    buf b_patterndetect (PATTERNDETECT,  pdet_o_mux);
    buf b_patternbdetect (PATTERNBDETECT, pdetb_o_mux);
    buf b_underflow (UNDERFLOW, underflow_o);

//-----------------------------------------------------
//-----------   Inputs --------------------------------
//-----------------------------------------------------
    buf b_gsr (gsr_in, GSR);

`ifndef XIL_TIMING
      assign a_dly = A;
      assign acin_dly = ACIN;
      assign alumode_dly = ALUMODE;
      assign b_dly = B;
      assign bcin_dly = BCIN;
      assign c_dly = C;
      assign carrycascin_dly = CARRYCASCIN;
      assign carryin_dly = CARRYIN;
      assign carryinsel_dly = CARRYINSEL;
      assign cea1_dly = CEA1;
      assign cea2_dly = CEA2;
      assign cead_dly = CEAD;
      assign cealumode_dly = CEALUMODE;
      assign ceb1_dly = CEB1;
      assign ceb2_dly = CEB2;
      assign cec_dly = CEC;
      assign cecarryin_dly = CECARRYIN;
      assign cectrl_dly = CECTRL;
      assign ced_dly = CED;
      assign ceinmode_dly = CEINMODE;
      assign cem_dly = CEM;
      assign cep_dly = CEP;
      assign clk_dly = CLK;
      assign d_dly = D;
      assign inmode_dly = INMODE;
      assign multsignin_dly = MULTSIGNIN;
      assign opmode_dly = OPMODE;
      assign pcin_dly = PCIN;
      assign rsta_dly = RSTA;
      assign rstallcarryin_dly = RSTALLCARRYIN;
      assign rstalumode_dly = RSTALUMODE;
      assign rstb_dly = RSTB;
      assign rstc_dly = RSTC;
      assign rstctrl_dly = RSTCTRL;
      assign rstd_dly = RSTD;
      assign rstinmode_dly = RSTINMODE;
      assign rstm_dly = RSTM;
      assign rstp_dly = RSTP;
`endif //  `ifndef XIL_TIMING

      assign a_in             = a_dly;
      assign acin_in          = acin_dly;
      assign alumode_in       = alumode_dly ^ IS_ALUMODE_INVERTED_BIN;
      assign b_in             = b_dly;
      assign bcin_in          = bcin_dly;
      assign c_in             = c_dly;
      assign carrycascin_in   = carrycascin_dly;
      assign carryin_in       = carryin_dly ^ IS_CARRYIN_INVERTED_BIN;
      assign carryinsel_in    = carryinsel_dly;
      assign cea1_in          = cea1_dly;
      assign cea2_in          = cea2_dly;
      assign cead_in          = cead_dly;
      assign cealumode_in     = cealumode_dly;
      assign ceb1_in          = ceb1_dly;
      assign ceb2_in          = ceb2_dly;
      assign cec_in           = cec_dly;
      assign cecarryin_in     = cecarryin_dly;
      assign cectrl_in        = cectrl_dly;
      assign ced_in           = ced_dly;
      assign ceinmode_in      = ceinmode_dly;
      assign cem_in           = cem_dly;
      assign cep_in           = cep_dly;
      assign clk_in           = clk_dly ^ IS_CLK_INVERTED_BIN;
      assign d_in             = d_dly;
      assign inmode_in        = inmode_dly ^ IS_INMODE_INVERTED_BIN;
      assign multsignin_in    = multsignin_dly;
      assign opmode_in        = opmode_dly ^ IS_OPMODE_INVERTED_BIN;
      assign pcin_in          = pcin_dly;
      assign rsta_in          = rsta_dly;
      assign rstallcarryin_in = rstallcarryin_dly;
      assign rstalumode_in    = rstalumode_dly;
      assign rstb_in          = rstb_dly;
      assign rstc_in          = rstc_dly;
      assign rstctrl_in       = rstctrl_dly;
      assign rstd_in          = rstd_dly;
      assign rstinmode_in     = rstinmode_dly;
      assign rstm_in          = rstm_dly;
      assign rstp_in          = rstp_dly;

//*** GLOBAL hidden GSR pin
  always @(gsr_in) begin
    if (gsr_in) begin
      assign qcarryin_o_reg0 = 1'b0;
      assign qcarryinsel_o_reg1 = 3'b0;
      assign qopmode_o_reg1 = 7'b0;
      assign qalumode_o_reg1 = 4'b0;
      assign qa_o_reg1 = 30'b0;
      assign qa_o_reg2 = 30'b0;
      assign qb_o_reg1 = 18'b0;
      assign qb_o_reg2 = 18'b0;
      assign qc_o_reg1 = 48'b0;
      assign qp_o_reg1 = 48'b0;
      assign qmult_o_reg = 43'b0;
      assign pdet_o_reg1 = 1'b0;
      assign pdet_o_reg2 = 1'b0;
      assign pdetb_o_reg1 = 1'b0;
      assign pdetb_o_reg2 = 1'b0;
// 577648 commented out the following line
//    assign carryout_o_reg = 4'b0;
      assign carrycascout_o_reg = 1'b0;
      assign qmultsignout_o_reg = 1'b0;
      assign qd_o_reg1 = 25'b0;
      assign qad_o_reg1 = 25'b0;
      assign qinmode_o_reg = 5'b0;
//      assign mult_o = 43'b0;
    end
    else begin
      deassign qcarryin_o_reg0;
      deassign qcarryinsel_o_reg1;
      deassign qopmode_o_reg1;
      deassign qalumode_o_reg1;
      deassign qa_o_reg1;
      deassign qa_o_reg2;
      deassign qb_o_reg1;
      deassign qb_o_reg2;
      deassign qc_o_reg1;
      deassign qp_o_reg1;
      deassign qmult_o_reg;
      deassign pdet_o_reg1;
      deassign pdet_o_reg2;
      deassign pdetb_o_reg1;
      deassign pdetb_o_reg2;
// 577648 commented out the following line
//    deassign carryout_o_reg;
      deassign carrycascout_o_reg;
      deassign qmultsignout_o_reg;
      deassign qd_o_reg1;
      deassign qad_o_reg1;
      deassign qinmode_o_reg;
//      deassign mult_o;
    end
  end


    initial begin
  opmode_valid_flag <= 1;
  invalid_opmode <= 1;

        //-------- A_INPUT check

  case (A_INPUT)
             "DIRECT", "CASCADE" : ;
              default : begin
                       $display("Attribute Syntax Error : The attribute A_INPUT on DSP48E1 instance %m is set to %s.  Legal values for this attribute are DIRECT or CASCADE.", A_INPUT);
                #1 $finish;
                        end
  endcase

        //-------- ALUMODEREG check

  case (ALUMODEREG)
            0, 1 : ;
            default : begin
                    $display("Attribute Syntax Error : The attribute ALUMODEREG on DSP48E1 instance %m is set to %d.  Legal values for this attribute are 0, 1.", ALUMODEREG);
                    #1 $finish;
                end
  endcase

        //-------- AREG check

  case (AREG)
            0, 1, 2 : ;
            default : begin
                    $display("Attribute Syntax Error : The attribute AREG on DSP48E1 instance %m is set to %d.  Legal values for this attribute are 0, 1 or 2.", AREG);
                    #1 $finish;
                end
  endcase

        //-------- (ACASCREG) and (ACASCREG vs AREG) check

  case (AREG)
            0 : if(AREG != ACASCREG) begin
                    $display("Attribute Syntax Error : The attribute ACASCREG  on DSP48E1 instance %m is set to %d.  ACASCREG has to be set to 0 when attribute AREG = 0.", ACASCREG);
                    #1 $finish;
                end
            1 : if(AREG != ACASCREG) begin
                    $display("Attribute Syntax Error : The attribute ACASCREG  on DSP48E1 instance %m is set to %d.  ACASCREG has to be set to 1 when attribute AREG = 1.", ACASCREG);
                    #1 $finish;
                end
            2 : if((AREG != ACASCREG) && ((AREG-1) != ACASCREG)) begin
                    $display("Attribute Syntax Error : The attribute ACASCREG  on DSP48E1 instance %m is set to %d.  ACASCREG has to be set to either 2 or 1 when attribute AREG = 2.", ACASCREG);
                    #1 $finish;
                end
            default : ;
  endcase

        //-------- B_INPUT check

  case (B_INPUT)
             "DIRECT", "CASCADE" : ;
              default : begin
                       $display("Attribute Syntax Error : The attribute B_INPUT on DSP48E1 instance %m is set to %s.  Legal values for this attribute are DIRECT or CASCADE.", B_INPUT);
                #1 $finish;
                        end
  endcase


        //-------- BREG check

  case (BREG)
            0, 1, 2 : ;
            default : begin
                    $display("Attribute Syntax Error : The attribute BREG on DSP48E1 instance %m is set to %d.  Legal values for this attribute are 0, 1 or 2.", BREG);
                    #1 $finish;
                end
  endcase

        //-------- (BCASCREG) and (BCASCREG vs BREG) check

  case (BREG)
            0 : if(BREG != BCASCREG) begin
                    $display("Attribute Syntax Error : The attribute BCASCREG  on DSP48E1 instance %m is set to %d.  BCASCREG has to be set to 0 when attribute BREG = 0.", BCASCREG);
                    #1 $finish;
                end
            1 : if(BREG != BCASCREG) begin
                    $display("Attribute Syntax Error : The attribute BCASCREG  on DSP48E1 instance %m is set to %d.  BCASCREG has to be set to 1 when attribute BREG = 1.", BCASCREG);
                    #1 $finish;
                end
            2 : if((BREG != BCASCREG) && ((BREG-1) != BCASCREG)) begin
                    $display("Attribute Syntax Error : The attribute BCASCREG  on DSP48E1 instance %m is set to %d.  BCASCREG has to be set to either 2 or 1 when attribute BREG = 2.", BCASCREG);
                    #1 $finish;
                end
            default : ;
  endcase

        //-------- CARRYINREG check

  case (CARRYINREG)
            0, 1 : ;
            default : begin
                    $display("Attribute Syntax Error : The attribute CARRYINREG on DSP48E1 instance %m is set to %d.  Legal values for this attribute are 0, 1.", CARRYINREG);
                    #1 $finish;
                end
  endcase

        //-------- CARRYINSELREG check

  case (CARRYINSELREG)
            0, 1 : ;
            default : begin
                    $display("Attribute Syntax Error : The attribute CARRYINSELREG on DSP48E1 instance %m is set to %d.  Legal values for this attribute are 0, 1.", CARRYINSELREG);
                    #1 $finish;
                end
  endcase

        //-------- CREG check

  case (CREG)
            0, 1 : ;
            default : begin
                    $display("Attribute Syntax Error : The attribute CREG on DSP48E1 instance %m is set to %d.  Legal values for this attribute are 0, or 1.", CREG);
                    #1 $finish;
                end
  endcase


        //-------- OPMODEREG check

  case (OPMODEREG)
            0, 1 : ;
            default : begin
                    $display("Attribute Syntax Error : The attribute OPMODEREG on DSP48E1 instance %m is set to %d.  Legal values for this attribute are 0, 1.", OPMODEREG);
                    #1 $finish;
                end
  endcase

        //-------- USE_MULT

        case (USE_MULT)
            "NONE", "MULTIPLY", "DYNAMIC" : ;
            default : begin
                          $display("Attribute Syntax Error : The attribute USE_MULT on DSP48E1 instance %m is set to %s. Legal values for this attribute are MULTIPLY, DYNAMIC or NONE.", USE_MULT);
                          #1 $finish;
                     end
/*
            "MULT" : if (MREG != 0) begin
                               $display("Attribute Syntax Error : The attribute USE_MULT on DSP48E1 instance %m is set to %s. This requires attribute MREG to be set to 0.", USE_MULT);
                               #1 $finish;
                        end
            "MULT_S" : if (MREG != 1) begin
                               $display("Attribute Syntax Error : The attribute USE_MULT on DSP48E1 instance %m is set to %s. This requires attribute MREG to be set to 1.", USE_MULT);
                               #1 $finish;
                        end
            default : begin
                          $display("Attribute Syntax Error : The attribute USE_MULT on DSP48E1 instance %m is set to %s. Legal values for this attribute are NONE, MULT or MULT_S.", USE_MULT);
                          #1 $finish;
                     end
*/
        endcase

        //-------- USE_PATTERN_DETECT

        case (USE_PATTERN_DETECT)
            "PATDET", "NO_PATDET" : ;
            default : begin
               $display("Attribute Syntax Error : The attribute USE_PATTERN_DETECT on DSP48E1 instance %m is set to %s.  Legal values for this attribute are PATDET or NO_PATDET.",  USE_PATTERN_DETECT);
               #1 $finish;
            end
        endcase

        //-------- AUTORESET_PATDET check

        case (AUTORESET_PATDET)
            "NO_RESET", "RESET_MATCH", "RESET_NOT_MATCH" : ;
            default : begin
               $display("Attribute Syntax Error : The attribute AUTORESET_PATDET on DSP48E1 instance %m is set to %s.  Legal values for this attribute are  NO_RESET or RESET_MATCH or RESET_NOT_MATCH.",  AUTORESET_PATDET);
               #1 $finish;
            end
        endcase

        //-------- SEL_PATTERN check

        case(SEL_PATTERN)
           "PATTERN", "C" : ;
            default : begin
                         $display("Attribute Syntax Error : The attribute SEL_PATTERN on DSP48E1 instance %m is set to %s.  Legal values for this attribute are PATTERN or C.", SEL_PATTERN);
                         #1 $finish;
                      end
  endcase

        //-------- SEL_MASK check

        case(SEL_MASK)
            "MASK", "C", "ROUNDING_MODE1", "ROUNDING_MODE2" : ;
             default : begin
                         $display("Attribute Syntax Error : The attribute SEL_MASK on DSP48E1 instance %m is set to %s.  Legal values for this attribute are MASK or C or ROUNDING_MODE1 or ROUNDING_MODE2.", SEL_MASK);
                          #1 $finish;
                       end
  endcase

        //-------- MREG check

  case (MREG)
            0, 1 : ;
            default : begin
                    $display("Attribute Syntax Error : The attribute MREG on DSP48E1 instance %m is set to %d.  Legal values for this attribute are 0, 1.", MREG);
                    #1 $finish;
                end
  endcase


        //-------- PREG check

  case (PREG)
            0, 1 : ;
            default : begin
                    $display("Attribute Syntax Error : The attribute PREG on DSP48E1 instance %m is set to %d.  Legal values for this attribute are 0, 1.", PREG);
                    #1 $finish;
                end
  endcase


        #100010 ping_opmode_drc_check <= 1;

    
//*********************************************************
//*** ADDITIONAL DRC  
//*********************************************************
// CR 219407  --  (1)
// old ask vicv
/*
    if((AUTORESET_PATTERN_DETECT == "TRUE") && (USE_PATTERN_DETECT == "NO_PATDET")) begin
         $display("Attribute Syntax Error : The attribute USE_PATTERN_DETECT on DSP48E1 instance %m must be set to PATDET in order to use AUTORESET_PATTERN_DETECT equals TRUE. Failure to do so could make timing reports inaccurate. ");
     end
*/
//*********************************************************
//***  new attribute DRC
//*********************************************************

        //-------- ADREG check

  case (ADREG)
            0, 1 : ;
            default : begin
                    $display("Attribute Syntax Error : The attribute ADREG on DSP48E1 instance %m is set to %d.  Legal values for this attribute are 0, 1.", ADREG);
                    #1 $finish;
                end
  endcase

        //-------- DREG check

  case (DREG)
            0, 1 : ;
            default : begin
                    $display("Attribute Syntax Error : The attribute DREG on DSP48E1 instance %m is set to %d.  Legal values for this attribute are 0, 1.", DREG);
                    #1 $finish;
                end
  endcase

        //-------- INMODEREG check

  case (INMODEREG)
            0, 1 : ;
            default : begin
                    $display("Attribute Syntax Error : The attribute INMODEREG on DSP48E1 instance %m is set to %d.  Legal values for this attribute are 0, 1.", INMODEREG);
                    #1 $finish;
                end
  endcase

        //-------- USE_DPORT

        case (USE_DPORT)
            "TRUE", "FALSE" : ;
            default : begin
               $display("Attribute Syntax Error : The attribute USE_DPORT on DSP48E1 instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.",  USE_DPORT);
               #1 $finish;
            end
        endcase

        if ((USE_MULT == "NONE") && (MREG !== 0)) begin
              $display("Error : [Unisim %s-10] : Attribute USE_MULT is set to \"NONE\" and MREG is set to %2d. MREG must be set to 0 when the multiplier is not used. Instance %m", MODULE_NAME, MREG);
               #1 $finish;
        end

    end


//*********************************************************
//**********  INMODE signal registering        ************
//*********************************************************
// new 
    always @(posedge clk_in) begin
       if (rstinmode_in)
          qinmode_o_reg <= 5'b0;
       else if (ceinmode_in)
          qinmode_o_reg <= inmode_in;
    end

    generate 
       case (INMODEREG)
          0: begin 
             always @(inmode_in)
                qinmode_o_mux <= inmode_in;
    end

          1: begin 
             always @(qinmode_o_reg)
                qinmode_o_mux <= qinmode_o_reg;
    end
       endcase
    endgenerate 

//*********************************************************
//*** Input register A with 2 level deep of registers
//*********************************************************

    generate 
       case (A_INPUT)
          "DIRECT"  : always @(a_in)    a_o_mux <= a_in;
          "CASCADE" : always @(acin_in) a_o_mux <= acin_in;
       endcase
    endgenerate 

    generate 
       case (AREG)
          1 : begin
              always @(posedge clk_in) begin
           if (rsta_in) begin
                    qa_o_reg1 <= 30'b0;
                    qa_o_reg2 <= 30'b0;
                 end
                 else begin
                      if (cea1_in)
                          qa_o_reg1 <= a_o_mux;
                      if (cea2_in)
                          qa_o_reg2 <= a_o_mux;
                 end
              end
          end

          2 : begin
              always @(posedge clk_in) begin
           if (rsta_in) begin
                    qa_o_reg1 <= 30'b0;
                    qa_o_reg2 <= 30'b0;
                 end
                 else begin
                      if (cea1_in)
                          qa_o_reg1 <= a_o_mux;
                      if (cea2_in)
                          qa_o_reg2 <= qa_o_reg1;
                 end
              end
          end
       endcase
    endgenerate 

    generate 
       case (AREG)
          0: always @(a_o_mux) qa_o_mux <= a_o_mux;
          1,2 : always @(qa_o_reg2) qa_o_mux <= qa_o_reg2;
       endcase
    endgenerate 

    generate 
       case (ACASCREG)
          1: always @(qa_o_mux or qa_o_reg1) begin
                 if(AREG == 2)
                    qacout_o_mux <= qa_o_reg1;
                 else
                    qacout_o_mux <= qa_o_mux;
             end
          0,2 : always @(qa_o_mux) qacout_o_mux <= qa_o_mux;
       endcase
    endgenerate 

// new  
    
   assign a_preaddsub = qinmode_o_mux[1]? 25'b0:(qinmode_o_mux[0]?qa_o_reg1[24:0]:qa_o_mux[24:0]);

//*********************************************************
//*** Input register B with 2 level deep of registers
//*********************************************************

    generate 
       case (B_INPUT)
          "DIRECT"  : always @(b_in)    b_o_mux <= b_in;
          "CASCADE" : always @(bcin_in) b_o_mux <= bcin_in;
       endcase
    endgenerate 

    generate 
       case (BREG)
          1 : begin
              always @(posedge clk_in) begin
           if (rstb_in) begin
                      qb_o_reg1 <= 18'b0;
                      qb_o_reg2 <= 18'b0;
                 end
                 else begin
                      if (ceb1_in)
                          qb_o_reg1 <= b_o_mux;
                      if (ceb2_in)
                          qb_o_reg2 <= b_o_mux;
                 end
              end
          end

          2 : begin
              always @(posedge clk_in) begin
           if (rstb_in) begin
                    qb_o_reg1 <= 18'b0;
                    qb_o_reg2 <= 18'b0;
                 end
                 else begin
                      if (ceb1_in)
                          qb_o_reg1 <= b_o_mux;
                      if (ceb2_in)
                          qb_o_reg2 <= qb_o_reg1;
                 end
              end
          end
       endcase
    endgenerate 

    generate 
       case (BREG)
          0: always @(b_o_mux) qb_o_mux <= b_o_mux;
          1,2 : always @(qb_o_reg2) qb_o_mux <= qb_o_reg2;
       endcase
    endgenerate 

    generate
       case (BCASCREG)
          1: always @(qb_o_mux or qb_o_reg1) begin
                 if(BREG == 2)
                    qbcout_o_mux <= qb_o_reg1;
                 else
                    qbcout_o_mux <= qb_o_mux;
             end
          0,2 : always @(qb_o_mux) qbcout_o_mux <= qb_o_mux;
       endcase
    endgenerate


// new
    
   assign b_mult = qinmode_o_mux[4]?qb_o_reg1:qb_o_mux;

//*********************************************************
//*** Input register C with 1 level deep of register
//*********************************************************

    always @(posedge clk_in) begin
  if (rstc_in)
            qc_o_reg1 <= 48'b0;
  else if (cec_in)
            qc_o_reg1 <= c_in;
    end


    generate
       case (CREG)
          0 : always @(c_in) qc_o_mux <= c_in;
          1 : always @(qc_o_reg1) qc_o_mux <= qc_o_reg1;
       endcase
    endgenerate


// new

//*********************************************************
//*** Input register D with 1 level deep of register
//*********************************************************
    always @(posedge clk_in) begin
  if (rstd_in)
            qd_o_reg1 <= 25'b0;
  else if (ced_in)
            qd_o_reg1 <= d_in;
    end

    generate
       case (DREG)
          0 : always @(d_in) qd_o_mux <= d_in;
          1 : always @(qd_o_reg1) qd_o_mux <= qd_o_reg1;
       endcase
    endgenerate




//*********************************************************
//*** Preaddsub AD register with 1 level deep of register
//*********************************************************
// new  
      assign ad_addsub = qinmode_o_mux[3]?(-a_preaddsub + (qinmode_o_mux[2]?qd_o_mux:25'b0)):(a_preaddsub + (qinmode_o_mux[2]?qd_o_mux:25'b0));

    always @(posedge clk_in) begin
  if (rstd_in)
            qad_o_reg1 <= 25'b0;
  else if (cead_in)
            qad_o_reg1 <= ad_addsub;
    end

    generate
       case (ADREG)
          0 : always @(ad_addsub) qad_o_mux <= ad_addsub;
          1 : always @(qad_o_reg1) qad_o_mux <= qad_o_reg1;
       endcase
    endgenerate

/*------------------------------------------------- */
/*------------------------------------------------- */

   assign ad_mult = (USE_DPORT=="TRUE")? qad_o_mux : a_preaddsub;
//*********************************************************

//*********************************************************
//***************      25x18 Multiplier     ***************
//*********************************************************
// 05/26/05 -- FP -- Added warning for invalid mult when USE_MULT=NONE
// SIMD=FOUR12 and SIMD=TWO24
// Made mult_o to be "X"

    always @(qopmode_o_mux) begin
       if(qopmode_o_mux[3:0] == 4'b0101)
          if((USE_MULT == "NONE") || (USE_SIMD == "TWO24") || (USE_SIMD == "FOUR12")) 
               $display("OPMODE Input Warning : The OPMODE[3:0] %b to DSP48E1 instance %m is invalid when using attributes USE_MULT = NONE, or USE_SIMD = TWO24 or FOUR12 at %.3f ns.", qopmode_o_mux[3:0], $time/1000.0);
    end

//    assign mult_o = ((USE_MULT == "NONE") || (USE_SIMD == "TWO24") || (USE_SIMD == "FOUR12"))? 43'b0 : {{18{ad_mult[24]}}, ad_mult[24:0]} * {{25{b_mult[17]}}, b_mult};

    assign mult_o = ((USE_MULT == "NONE") || (USE_SIMD != "ONE48")) ? 43'b0 :
                    (carryinsel_in == 3'b010) ? 43'bx :
                    {{18{ad_mult[24]}}, ad_mult[24:0]} * {{25{b_mult[17]}}, b_mult};

//   always @(*) begin
//     if ((USE_MULT == "NONE") || (USE_SIMD == "TWO24") || (USE_SIMD == "FOUR12"))
//       mult_o = 43'b0;
//     else if (qcarryinsel_o_mux == 3'b010) 
//       mult_o = 43'bx;
//     else
//       mult_o = {{18{ad_mult[24]}}, ad_mult[24:0]} * {{25{b_mult[17]}}, b_mult};
//   end

    always @(posedge clk_in) begin
      if (rstm_in) begin
        qmult_o_reg <= 43'b0;
      end
      else if (cem_in) begin
        qmult_o_reg <= mult_o;
      end
    end

    always @ (mult_o, qmult_o_reg, qcarryinsel_o_mux) begin
      if (qcarryinsel_o_mux == 3'b010)  begin
        qmult_o_mux = 43'bx ;
      end else if (MREG == 1) begin 
        qmult_o_mux = qmult_o_reg;
      end else
        qmult_o_mux = mult_o;
      end

//    generate
//       case (MREG)
//          0 : always @(mult_o) qmult_o_mux <= mult_o;
//          1 : always @(qmult_o_reg) qmult_o_mux <= qmult_o_reg;
//       endcase
//    endgenerate


//*** X mux
// ask jmt

    always @(qp_o_mux or qa_o_mux or qb_o_mux or qmult_o_mux or qopmode_o_mux[1:0] or qcarryinsel_o_mux) begin
//add post 2014.4 
// if (qcarryinsel_o_mux == 3'b010) && (OPMODEREG == 0) begin
//   qx_o_mux <= 48'bx;
// else
  case (qopmode_o_mux[1:0])
              2'b00 : qx_o_mux <= 48'b0;
              2'b01 : qx_o_mux <= {{5{qmult_o_mux[MSB_A_MULT + MSB_B_MULT + 1]}}, qmult_o_mux};
              2'b10 : qx_o_mux <= qp_o_mux;
// new DRC 
              2'b11 : begin
                         if((USE_MULT == "MULTIPLY") && (
                                  (AREG==0 && BREG==0 && MREG==0) ||
                                  (AREG==0 && BREG==0 && PREG==0) ||
                                  (MREG==0 && PREG==0)))
                               $display("OPMODE Input Warning : The OPMODE[1:0] %b to DSP48E1 instance %m is invalid when using attributes USE_MULT = MULTIPLY at %.3f ns. Please set USE_MULT to either NONE or DYNAMIC.", qopmode_o_mux[1:0], $time/1000.0);
                   else
                            qx_o_mux <=  {qa_o_mux[MSB_A:0], qb_o_mux[MSB_B:0]};
                end

            default : begin
                end
  endcase
    end


//*** Y mux

// 08-06-08  
// IR 478378
    wire [47:0] y_mac_cascd = (qopmode_o_mux[6:4] == 3'b100) ? {48{multsignin_in}} : {48{1'b1}};

    always @(qc_o_mux or qopmode_o_mux[3:2] or qcarryinsel_o_mux or y_mac_cascd) begin
//add post 2014.4 
// if (qcarryinsel_o_mux == 3'b010) && (OPMODEREG == 0) begin
//   qy_o_mux <= 48'bx;
// else
  case (qopmode_o_mux[3:2])
              2'b00 : qy_o_mux <= 48'b0;
              2'b01 : qy_o_mux <= 48'b0;
// 08-06-08  
              2'b10 : qy_o_mux <= y_mac_cascd;                // choose all ones or mult-sign-extend
              2'b11 : qy_o_mux <= qc_o_mux;
            default : begin
                end
  endcase
    end


//*** Z mux

    always @(qp_o_mux or qc_o_mux or pcin_in or qopmode_o_mux[6:4] or qcarryinsel_o_mux) begin
// ask jmt
//add post 2014.4 
// if (qcarryinsel_o_mux == 3'b010) && (OPMODEREG == 0) begin
//   qz_o_mux <= 48'bx;
// else
  casex (qopmode_o_mux[6:4])
             3'b000 : qz_o_mux <= 48'b0;
             3'b001 : qz_o_mux <= pcin_in;
             3'b010 : qz_o_mux <= qp_o_mux;
             3'b011 : qz_o_mux <= qc_o_mux;
             3'b100 : qz_o_mux <= qp_o_mux;
             3'b101 : qz_o_mux <= {{17{pcin_in[47]}}, pcin_in[47:17]};
// ask jmt 
             3'b11x : qz_o_mux <= {{17{qp_o_mux[47]}}, qp_o_mux[47:17]};
            default : begin
                end
  endcase
    end



//*** CarryInSel and OpMode with 1 level of register
    always @(posedge clk_in) begin
  if (rstctrl_in) begin
            qcarryinsel_o_reg1 <= 3'b0;
            qopmode_o_reg1 <= 7'b0;
  end  
  else if (cectrl_in) begin
            qcarryinsel_o_reg1 <= carryinsel_in;
            qopmode_o_reg1 <= opmode_in;
  end
    end

    generate
       case (CARRYINSELREG)
          0 : always @(carryinsel_in) qcarryinsel_o_mux <= carryinsel_in;
          1 : always @(qcarryinsel_o_reg1) qcarryinsel_o_mux <= qcarryinsel_o_reg1;
       endcase
    endgenerate


//CR 219047 (3) 

    always @(qcarryinsel_o_mux or carrycascin_in or multsignin_in or qopmode_o_mux) begin
      if(qcarryinsel_o_mux == 3'b010) begin 
        if(!((multsignin_in === 1'bx) || (cci_drc_msg == 1'b1) ||
             ((qopmode_o_mux == 7'b1001000) && !(multsignin_in === 1'bx))  ||
             ((multsignin_in == 1'b0) && (carrycascin_in == 1'b0)))) begin
          $display("DRC warning : CARRYCASCIN can only be used in the current DSP48E1 instance %m if the previous DSP48E1 is performing a two input ADD or SUBTRACT operation, or the current DSP48E1 is configured in the MAC extend opmode 7'b1001000 at %.3f ns.", $time/1000.0);
          cci_drc_msg = 1'b1;
        end  
        if(!((multsignin_in === 1'bx) || (qopmode_o_mux[3:0] != 4'b0101))) begin 
          $display("DRC warning : CARRYINSEL is set to 010 with OPMODE set to multiplication (xxx0101). This is an illegal mode and may show deviation between simulation results and hardware behavior. DSP48E1 instance %m at %.3f ns.", $time/1000.0);
        end  
        if(!((multsignin_in === 1'bx) || (cis_drc_msg == 1'b1) ||
             (OPMODEREG == 1'b1))) begin 
          $display("DRC warning : CARRYINSEL is set to 010 with OPMODEREG set to 0. This causes unknown values after reset occurs. It is suggested to use OPMODEREG = 1 when cascading large adders. DSP48E1 instance %m at %.3f ns.", $time/1000.0);
          cis_drc_msg = 1'b1;
        end  
      end  
    end 

    generate
       case (OPMODEREG)
          0 : always @(opmode_in) qopmode_o_mux <= opmode_in;
          1 : always @(qopmode_o_reg1) qopmode_o_mux <= qopmode_o_reg1;
       endcase
    endgenerate


//*** ALUMODE with 1 level of register
    always @(posedge clk_in) begin
  if (rstalumode_in)
            qalumode_o_reg1 <= 4'b0;
  else if (cealumode_in)
            qalumode_o_reg1 <= alumode_in;
    end


    generate
       case (ALUMODEREG)
          0 : always @(alumode_in) qalumode_o_mux <= alumode_in;
          1 : always @(qalumode_o_reg1) qalumode_o_mux <= qalumode_o_reg1;
       endcase
    endgenerate

//------------------------------------------------------------------
//*** DRC for OPMODE
//------------------------------------------------------------------

    task deassign_xyz_mux;
        begin
            opmode_valid_flag = 1;
            invalid_opmode = 1;  // reset invalid opmode
        end
    endtask // deassign_xyz_mux

    
    task display_invalid_opmode;
        begin
            if (invalid_opmode) begin
                opmode_valid_flag = 0;
                invalid_opmode = 0;
                $display("OPMODE Input Warning : The OPMODE %b to DSP48E1 instance %m at %.3f ns requires attribute PREG set to 1.", qopmode_o_mux, $time/1000.0);
            end
        end
    endtask // display_invalid_opmode

    always @(ping_opmode_drc_check or qalumode_o_mux or qopmode_o_mux or qcarryinsel_o_mux ) begin

      if ($time > 100000) begin  // no check at first 100ns
        case (qalumode_o_mux[3:2]) 
          2'b00 :
          //-- ARITHMETIC MODES DRC
            casex ({qopmode_o_mux, qcarryinsel_o_mux})
                10'bxxx0101010 : deassign_xyz_mux; // seperate drc above for these cases
                10'b0000000000 : deassign_xyz_mux;
                10'b0000010000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0000010010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0000011000 : deassign_xyz_mux;
                10'b0000011010 : deassign_xyz_mux;
// CR 573535                10'b0000011100 : deassign_xyz_mux;
                10'b0000011100 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0000101000 : deassign_xyz_mux;
                10'b0001000000 : deassign_xyz_mux;
                10'b0001010000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0001010010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0001011000 : deassign_xyz_mux;
                10'b0001011010 : deassign_xyz_mux;
// CR 573535                10'b0001011100 : deassign_xyz_mux;
                10'b0001011100 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0001100000 : deassign_xyz_mux;
                10'b0001100010 : deassign_xyz_mux;
// CR 573535                10'b0001100100 : deassign_xyz_mux;
                10'b0001100100 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0001110000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0001110010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0001110101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0001110111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0001111000 : deassign_xyz_mux;
                10'b0001111010 : deassign_xyz_mux;
// CR 573535                10'b0001111100 : deassign_xyz_mux;
                10'b0001111100 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0010000000 : deassign_xyz_mux;
                10'b0010010000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0010010101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0010010111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0010011000 : deassign_xyz_mux;
                10'b0010011001 : deassign_xyz_mux;
                10'b0010011011 : deassign_xyz_mux;
                10'b0010101000 : deassign_xyz_mux;
                10'b0010101001 : deassign_xyz_mux;
                10'b0010101011 : deassign_xyz_mux;
                10'b0010101110 : deassign_xyz_mux;
                10'b0011000000 : deassign_xyz_mux;
                10'b0011010000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0011010101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0011010111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0011011000 : deassign_xyz_mux;
                10'b0011011001 : deassign_xyz_mux;
                10'b0011011011 : deassign_xyz_mux;
                10'b0011100000 : deassign_xyz_mux;
                10'b0011100001 : deassign_xyz_mux;
                10'b0011100011 : deassign_xyz_mux;
                10'b0011100100 : deassign_xyz_mux;
                10'b0011110000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0011110101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0011110111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0011110001 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0011110011 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0011111000 : deassign_xyz_mux;
                10'b0011111001 : deassign_xyz_mux;
                10'b0011111011 : deassign_xyz_mux;
                10'b0100000000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0100000010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0100010000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0100010010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0100011000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0100011010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0100011101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0100011111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0100101000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0100101101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0100101111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101000000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101000010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101010000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101011000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101011101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101011111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101100000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101100010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101100101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101100111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101110000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101110101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101110111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101111000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101111101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0101111111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0110000000 : deassign_xyz_mux;
                10'b0110000010 : deassign_xyz_mux;
// CR 573535                10'b0110000100 : deassign_xyz_mux;
                10'b0110000100 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0110010000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0110010010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0110010101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0110010111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0110011000 : deassign_xyz_mux;
                10'b0110011010 : deassign_xyz_mux;
// CR 573535                10'b0110011100 : deassign_xyz_mux;
                10'b0110011100 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0110101000 : deassign_xyz_mux;
                10'b0110101110 : deassign_xyz_mux;
                10'b0111000000 : deassign_xyz_mux;
                10'b0111000010 : deassign_xyz_mux;
// CR 573535                10'b0111000100 : deassign_xyz_mux;
                10'b0111000100 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0111010000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0111010101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0111010111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0111011000 : deassign_xyz_mux;
                10'b0111100000 : deassign_xyz_mux;
                10'b0111100010 : deassign_xyz_mux;
                10'b0111110000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b0111111000 : deassign_xyz_mux;
                10'b1001000010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1010000000 : deassign_xyz_mux;
                10'b1010010000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1010010101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1010010111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1010011000 : deassign_xyz_mux;
                10'b1010011001 : deassign_xyz_mux;
                10'b1010011011 : deassign_xyz_mux;
                10'b1010101000 : deassign_xyz_mux;
                10'b1010101001 : deassign_xyz_mux;
                10'b1010101011 : deassign_xyz_mux;
                10'b1010101110 : deassign_xyz_mux;
                10'b1011000000 : deassign_xyz_mux;
                10'b1011010000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1011010101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1011010111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1011011000 : deassign_xyz_mux;
                10'b1011011001 : deassign_xyz_mux;
                10'b1011011011 : deassign_xyz_mux;
                10'b1011100000 : deassign_xyz_mux;
                10'b1011100001 : deassign_xyz_mux;
                10'b1011100011 : deassign_xyz_mux;
                10'b1011110000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1011110101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1011110111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1011110001 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1011110011 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1011111000 : deassign_xyz_mux;
                10'b1011111001 : deassign_xyz_mux;
                10'b1011111011 : deassign_xyz_mux;
                10'b1100000000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1100010000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1100011000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1100011101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1100011111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1100101000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1100101101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1100101111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1101000000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1101010000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1101011000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1101011101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1101011111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1101100000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1101100101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1101100111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1101110000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1101110101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1101110111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1101111000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1101111101 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                10'b1101111111 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                default : begin
                  if (invalid_opmode) begin
                     opmode_valid_flag = 0;
                     invalid_opmode = 0;
// CR 444150
                     if( ({qopmode_o_mux, qcarryinsel_o_mux} ==  10'b0000000010) && ((OPMODEREG==1) && (CARRYINSELREG ==0)) ) $display("DRC warning : The attribute CARRYINSELREG on DSP48E1 instance %m is set to %d. It is required to have CARRYINSELREG be set to 1 to match OPMODEREG, in order to ensure that the simulation model will match the hardware behavior in all use cases.", CARRYINSELREG);
                     $display("OPMODE Input Warning : The OPMODE %b to DSP48E1 instance %m is either invalid or the CARRYINSEL %b for that specific OPMODE is invalid at %.3f ns. This warning may be due to a mismatch in the OPMODEREG and CARRYINSELREG attribute settings. It is recommended that OPMODEREG and CARRYINSELREG always be set to the same value. ", qopmode_o_mux, qcarryinsel_o_mux, $time/1000.0);

                  end
                end

            endcase // case(OPMODE)

          2'b01, 2'b11 :
          //-- LOGIC MODES DRC
             case (qopmode_o_mux)
                7'b0000000 : deassign_xyz_mux;
                7'b0000010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b0000011 : deassign_xyz_mux;
                7'b0010000 : deassign_xyz_mux;
                7'b0010010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b0010011 : deassign_xyz_mux;
                7'b0100000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b0100010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b0100011 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b0110000 : deassign_xyz_mux;
                7'b0110010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b0110011 : deassign_xyz_mux;
                7'b1010000 : deassign_xyz_mux;
                7'b1010010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b1010011 : deassign_xyz_mux;
                7'b1100000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b1100010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b1100011 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b0001000 : deassign_xyz_mux;
                7'b0001010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b0001011 : deassign_xyz_mux;
                7'b0011000 : deassign_xyz_mux;
                7'b0011010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b0011011 : deassign_xyz_mux;
                7'b0101000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b0101010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b0101011 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b0111000 : deassign_xyz_mux;
                7'b0111010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b0111011 : deassign_xyz_mux;
                7'b1011000 : deassign_xyz_mux;
                7'b1011010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b1011011 : deassign_xyz_mux;
                7'b1101000 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b1101010 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
                7'b1101011 : if (PREG != 1) display_invalid_opmode; else deassign_xyz_mux;
              default : begin
                 if (invalid_opmode) begin

                    opmode_valid_flag = 0;
                    invalid_opmode = 0;
                    $display("OPMODE Input Warning : The OPMODE %b to DSP48E1 instance %m is invalid for LOGIC MODES at %.3f ns.", qopmode_o_mux, $time/1000.0);

                 end
              end

            endcase // case(OPMODE)

        endcase // case(qalumode_o_mux)

     end // if ($time > 100000)

    end // always @ (qopmode_o_mux)


//--####################################################################
//--#####                         ALU                              #####
//--####################################################################

  wire mult_cout = ~qp_o_mux[42];
  reg  [MSB_ALU_FULL:0] co;
  reg  [MSB_ALU_FULL:0] s;
  wire [MSB_ALU_FULL:0] comux,smux;
  wire [MSB_CARRYOUT:0] carryout_o_hw;
  wire [MSB_CARRYOUT:0] carryout_o;
  wire tmp_carrycascout_in;

  always @ (qx_o_mux or qy_o_mux or qz_o_mux or qalumode_o_mux[0]) begin
    if (qalumode_o_mux[0]) begin
       co = ((qx_o_mux & qy_o_mux)|((~qz_o_mux) & qy_o_mux)|(qx_o_mux & (~qz_o_mux)));
       s  = (~qz_o_mux) ^ qx_o_mux ^ qy_o_mux;
    end
    else begin
       co = ((qx_o_mux & qy_o_mux)|(qz_o_mux & qy_o_mux)|(qx_o_mux & qz_o_mux));
       s  =  qz_o_mux ^ qx_o_mux ^ qy_o_mux;
    end
  end

  assign comux = qalumode_o_mux[2] ? 0 : co;
  assign smux = qalumode_o_mux[3] ? co : s;

  // FINAL ADDER
  wire [12:0] s0 = {comux[10:0],qcarryin_o_mux}+smux[11:0];
  wire cout0 = (comux[11] + s0[12]);
  assign carryout_o_hw[0] = (qalumode_o_mux[0] & qalumode_o_mux[1]) ? ~cout0 : cout0;
  wire C1 = (USE_SIMD == "FOUR12") ? 1'b0 : s0[12];

  wire co11_lsb = (USE_SIMD == "FOUR12") ? 1'b0 : comux[11];
  wire [12:0] s1 = {comux[22:12],co11_lsb}+smux[23:12]+C1;
  wire cout1 = (comux[23] + s1[12]);
  assign carryout_o_hw[1] = (qalumode_o_mux[0] & qalumode_o_mux[1]) ? ~cout1 : cout1;
  wire C2 = ((USE_SIMD == "TWO24") || (USE_SIMD == "FOUR12")) ? 1'b0 : s1[12];

  wire co23_lsb = ((USE_SIMD == "TWO24") || (USE_SIMD == "FOUR12")) ? 
       1'b0 : comux[23];

  wire [12:0] s2 = {comux[34:24],co23_lsb}+smux[35:24]+C2;
  wire cout2 = (comux[35] + s2[12]);
  assign carryout_o_hw[2] = (qalumode_o_mux[0] & qalumode_o_mux[1]) ? ~cout2 : cout2;
  wire C3 = (USE_SIMD == "FOUR12") ? 1'b0 : s2[12];

  wire co35_lsb = (USE_SIMD == "FOUR12") ? 1'b0 : comux[35];
  wire [13:0] s3 = {comux[47:36],co35_lsb}+smux[47:36]+C3;
  wire cout3 = s3[12];

  assign carryout_o_hw[3] = (qalumode_o_mux[0] & qalumode_o_mux[1]) ? ~cout3 : cout3;

  wire   cout4 = s3[13];
//  assign carryout_o_hw[4] = (qalumode_o_mux[0] & qalumode_o_mux[1]) ? ~cout4 : cout4;

  assign alu_o  = qalumode_o_mux[1] ? ~{s3[11:0],s2[11:0],s1[11:0],s0[11:0]} :
                                {s3[11:0],s2[11:0],s1[11:0],s0[11:0]};
  // COMPUTE CARRYCASCOUT
  assign carrycascout_o = cout3;
  
  // COMPUTE MULTSIGNOUT
  // 08-06-08  assign  multsignout_o_opmode = (qopmode_o_mux[3:0] === 4'b100) ? multsignin_in  : ~qp_o_mux[42];
  // IR 478378 
  assign  multsignout_o_opmode = (qopmode_o_mux[6:4] === 3'b100) ? multsignin_in  : qmult_o_mux[42];

  // CR 523600 -- "X" carryout for multiply and logic operations
    assign carryout_o[3] = ((qopmode_o_mux[3:0] == 4'b0101) || (qalumode_o_mux[3:2] != 2'b00))? 1'bx : carryout_o_hw[3];
    assign carryout_o[2] = ((qopmode_o_mux[3:0] == 4'b0101) || (qalumode_o_mux[3:2] != 2'b00))? 1'bx : (USE_SIMD == "FOUR12") ? carryout_o_hw[2] : 1'bx;
    assign carryout_o[1] = ((qopmode_o_mux[3:0] == 4'b0101) || (qalumode_o_mux[3:2] != 2'b00))? 1'bx : ((USE_SIMD == "TWO24") ||  (USE_SIMD == "FOUR12")) ? carryout_o_hw[1] : 1'bx;
    assign carryout_o[0] = ((qopmode_o_mux[3:0] == 4'b0101) || (qalumode_o_mux[3:2] != 2'b00))? 1'bx : (USE_SIMD == "FOUR12") ? carryout_o_hw[0] : 1'bx;

//--########################### END ALU ################################
 
    
//*** CarryIn Mux and Register

//-------  input 0
    always @(posedge clk_in) begin
  if (rstallcarryin_in)
            qcarryin_o_reg0 <= 1'b0;
  else if (cecarryin_in)
            qcarryin_o_reg0 <= carryin_in;
    end

    generate
       case (CARRYINREG)
          0 : always @(carryin_in) qcarryin_o_mux0 <= carryin_in;
          1 : always @(qcarryin_o_reg0) qcarryin_o_mux0 <= qcarryin_o_reg0;
       endcase
    endgenerate

//-------  input 7
    always @(posedge clk_in) begin
  if (rstallcarryin_in)
            qcarryin_o_reg7 <= 1'b0;
// old  else if (cemultcarryin_in)
// new
  else if (cem_in)
// IR 478377 
            qcarryin_o_reg7 <=  ad_mult[24] ~^ b_mult[17];  // xnor
    end

//    always @(qa_o_mux[24] or qb_o_mux[17] or qcarryin_o_reg7) begin
    always @(ad_mult[24] or b_mult[17] or qcarryin_o_reg7) begin
// old  case (MULTCARRYINREG)
// new 
  case (MREG)
// IR 478377 
                  0 : qcarryin_o_mux7 <= ad_mult[24] ~^ b_mult[17];
                  1 : qcarryin_o_mux7 <= qcarryin_o_reg7;
            default : begin
                    $display("Attribute Syntax Error : The attribute MREG on DSP48E1 instance %m is set to %d.  Legal values for this attribute are 0 or 1.", MREG);
                    $finish;
                end
  endcase
    end
   
    reg qcarryin_o_mux_tmp;
    always @(qcarryin_o_mux0 or pcin_in[47] or carrycascin_in or carrycascout_o_mux or qp_o_mux[47] or qcarryin_o_mux7 or qcarryinsel_o_mux) begin
  case (qcarryinsel_o_mux)
              3'b000 : qcarryin_o_mux_tmp <= qcarryin_o_mux0;
              3'b001 : qcarryin_o_mux_tmp <= ~pcin_in[47];
              3'b010 : qcarryin_o_mux_tmp <= carrycascin_in;
              3'b011 : qcarryin_o_mux_tmp <= pcin_in[47];
              3'b100 : qcarryin_o_mux_tmp <= carrycascout_o_mux;
              3'b101 : qcarryin_o_mux_tmp <= ~qp_o_mux[47];
              3'b110 : qcarryin_o_mux_tmp <= qcarryin_o_mux7;
              3'b111 : qcarryin_o_mux_tmp <= qp_o_mux[47];
            default : begin
                end
  endcase
    end
    // disable carryin when performing logic operation
    always @(qcarryin_o_mux_tmp or qalumode_o_mux[3:2]) begin
      qcarryin_o_mux <= (qalumode_o_mux[3] || qalumode_o_mux[2]) ? 1'b0 : qcarryin_o_mux_tmp;
    end
 

//--####################################################################
//--#####                     AUTORESET_PATDET                     #####
//--####################################################################
    assign the_auto_reset_patdet = ((AUTORESET_PATDET == "RESET_MATCH") &&  pdet_o_reg1) 
                                                   ||
                                   ((AUTORESET_PATDET == "RESET_NOT_MATCH") &&  (pdet_o_reg2 && !pdet_o_reg1));
//--####################################################################
//--#####      CARRYOUT, CARRYCASCOUT. MULTSIGNOUT and PCOUT      ###### 
//--####################################################################
//*** register with 1 level of register
    always @(posedge clk_in) begin
        if(rstp_in || the_auto_reset_patdet)
             begin
               carryout_o_reg     <= 4'b0;
               carrycascout_o_reg <= 1'b0;
               qmultsignout_o_reg <= 1'b0;
               qp_o_reg1 <= 48'b0;
             end
        else if (cep_in) begin
                   carryout_o_reg     <= carryout_o;
                   carrycascout_o_reg <= carrycascout_o;
                   qmultsignout_o_reg <= multsignout_o_opmode;
                   qp_o_reg1 <= alu_o;
             end
    end

    generate 
       case (PREG)
          0: begin 
             always @(carryout_o)
                carryout_o_mux <= carryout_o;
             always @(carrycascout_o)
                carrycascout_o_mux <= carrycascout_o;
             always @(multsignout_o_opmode)
                 multsignout_o_mux <= multsignout_o_opmode;
             always @(alu_o)
                 qp_o_mux <= #1 alu_o;
    end

          1: begin 
             always @(carryout_o_reg)
                carryout_o_mux <= carryout_o_reg;
             always @(carrycascout_o_reg)
                carrycascout_o_mux <= carrycascout_o_reg;
             always @(qmultsignout_o_reg)
                 multsignout_o_mux <= qmultsignout_o_reg;
             always @(qp_o_reg1)
                 qp_o_mux <= qp_o_reg1;
    end
       endcase
    endgenerate



//CR 219047 (2)
// ask jmt whether i should comment this out 
/*
    always @(qmult_o_mux[(MSB_A_MULT+MSB_B_MULT+1)] or qopmode_o_mux[3:0]) begin
        if(qopmode_o_mux[3:0] == 4'b0101)
           multsignout_o_opmode = qmult_o_mux[(MSB_A_MULT+MSB_B_MULT+1)];
        else
           multsignout_o_opmode = 1'bx;
    end 
*/



//    assign carryout_x_o[4] =  carryout_o_mux[4];
// CR 510304 output X during multiply operation

    assign carryout_x_o[3] =  carryout_o_mux[3];
    assign carryout_x_o[2] =  (USE_SIMD == "FOUR12") ? carryout_o_mux[2] : 1'bx;
    assign carryout_x_o[1] =  ((USE_SIMD == "TWO24") ||  (USE_SIMD == "FOUR12")) ? carryout_o_mux[1] : 1'bx;
    assign carryout_x_o[0] =  (USE_SIMD == "FOUR12") ? carryout_o_mux[0] : 1'bx;


//--####################################################################
//--#####                    Pattern Detector                      #####
//--####################################################################


// new
    // selet pattern
    assign the_pattern = (SEL_PATTERN == "PATTERN") ? PATTERN : qc_o_mux; 

    // selet mask
    always @(qc_o_mux) begin
      if (USE_PATTERN_DETECT == "NO_PATDET") 
        the_mask <= {48{1'b1}};
      else
        case(SEL_MASK)
              "MASK" : the_mask <= MASK;
              "C"    : the_mask <= qc_o_mux;
              "ROUNDING_MODE1" :  the_mask     <=   ~qc_o_mux << 1;
              "ROUNDING_MODE2" :  the_mask     <=   ~qc_o_mux << 2;
               default : ;
        endcase
    end

    //--  now do the pattern detection
       
//    assign pdet_o = &(~(the_pattern ^ alu_o) | the_mask);  
//    assign pdetb_o = &((the_pattern ^ alu_o) | the_mask);  
    assign pdet_o  = (~opmode_valid_flag) ? 1'bx : &(~(the_pattern ^ alu_o) | the_mask);  
    assign pdetb_o = (~opmode_valid_flag) ? 1'bx : &((the_pattern ^ alu_o) | the_mask);  

//    assign pdet_o_mux  = (~opmode_valid_flag) ? 1'bx : (PREG == 1) ? pdet_o_reg1 : pdet_o;
//    assign pdetb_o_mux = (~opmode_valid_flag) ? 1'bx : (PREG == 1) ? pdetb_o_reg1 : pdetb_o;
    assign pdet_o_mux  = (PREG == 1) ? pdet_o_reg1 : pdet_o;
    assign pdetb_o_mux = (PREG == 1) ? pdetb_o_reg1 : pdetb_o;

//*** Output register PATTERN DETECT and UNDERFLOW / OVERFLOW 

    always @(posedge clk_in) begin
        if((rstp_in) || the_auto_reset_patdet) 
          begin 
            pdet_o_reg1  <= 1'b0;
            pdet_o_reg2  <= 1'b0;
            pdetb_o_reg1 <= 1'b0;
            pdetb_o_reg2 <= 1'b0;
          end
  else if(cep_in)
               begin
                 //-- the previous values are used in Underflow/Overflow
                 pdet_o_reg2  <= pdet_o_reg1;
                 pdet_o_reg1  <= pdet_o;
                 pdetb_o_reg2 <= pdetb_o_reg1;
                 pdetb_o_reg1 <= pdetb_o;
               end
    end

 
//--####################################################################
//--#####                    Underflow / Overflow                  #####
//--####################################################################
    generate if ((USE_PATTERN_DETECT == "PATDET") || (PREG == 1))
       begin         
          assign  overflow_o  = pdet_o_reg2 & !pdet_o_reg1 & !pdetb_o_reg1;
          assign  underflow_o = pdetb_o_reg2  & !pdet_o_reg1 & !pdetb_o_reg1;
       end
    else
       begin         
           assign overflow_o  = 1'bx;
           assign underflow_o = 1'bx;
       end
    endgenerate


`ifdef XIL_TIMING
//*** Timing Checks Start here

    always @(notifier) begin
      qp_o_mux <= 48'bx;
      qb_o_mux <= 18'bx;
    end

//    not (nrsta, rsta_in);
//    not (nrstb, rstb_in);
//    not (nrstc, rstc_in);
//    not (nrstp, rstp_in);
//    not (nrstallcarryin, rstallcarryin_in);
//    not (nrstctrl, rstctrl_in);

//    not (nrstinmode, rstinmode_in);
//    not (nrstd, rstd_in);

    assign cea12_enable = (((AREG == 1) && cea1_in) || ((AREG == 2) && (cea1_in || cea2_in)));
    assign ceb12_enable = (((BREG == 1) && ceb1_in) || ((BREG == 2) && (ceb1_in || ceb2_in)));

    assign a_en_n = (A_INPUT == "DIRECT") && cea12_enable && ~rsta_in && IS_CLK_INVERTED_BIN;
    assign a_en_p = (A_INPUT == "DIRECT") && cea12_enable && ~rsta_in && ~IS_CLK_INVERTED_BIN;
    assign b_en_n = (B_INPUT == "DIRECT") && ceb12_enable && ~rstb_in && IS_CLK_INVERTED_BIN;
    assign b_en_p = (B_INPUT == "DIRECT") && ceb12_enable && ~rstb_in && ~IS_CLK_INVERTED_BIN;

    assign acin_en_n = (A_INPUT == "CASCADE") && cea12_enable && ~rsta_in && IS_CLK_INVERTED_BIN;
    assign acin_en_p = (A_INPUT == "CASCADE") && cea12_enable && ~rsta_in && ~IS_CLK_INVERTED_BIN;
    assign bcin_en_n = (B_INPUT == "CASCADE") && ceb12_enable && ~rstb_in && IS_CLK_INVERTED_BIN;
    assign bcin_en_p = (B_INPUT == "CASCADE") && ceb12_enable && ~rstb_in && ~IS_CLK_INVERTED_BIN;

    assign carryin_en_n = cea12_enable && ceb12_enable && cecarryin_in && ~rsta_in && ~rstb_in && ~rstallcarryin_in && IS_CLK_INVERTED_BIN;
    assign carryin_en_p = cea12_enable && ceb12_enable && cecarryin_in && ~rsta_in && ~rstb_in && ~rstallcarryin_in && ~IS_CLK_INVERTED_BIN;
    assign carryinsel_en_n = cea12_enable && ceb12_enable && ~rsta_in && ~rstb_in && ~rstctrl_in && IS_CLK_INVERTED_BIN;
    assign carryinsel_en_p = cea12_enable && ceb12_enable && ~rsta_in && ~rstb_in && ~rstctrl_in && ~IS_CLK_INVERTED_BIN;
    assign opmode_en_n = cectrl_in && ~rstctrl_in && IS_CLK_INVERTED_BIN;
    assign opmode_en_p = cectrl_in && ~rstctrl_in && ~IS_CLK_INVERTED_BIN;
    assign pcin_en_n = cep_in && ~rstp_in && IS_CLK_INVERTED_BIN;
    assign pcin_en_p = cep_in && ~rstp_in && ~IS_CLK_INVERTED_BIN;

    assign c_en_n = cec_in && ~rstc_in && IS_CLK_INVERTED_BIN;
    assign c_en_p = cec_in && ~rstc_in && ~IS_CLK_INVERTED_BIN;

    assign inmode_en_n = ceinmode_in && ~rstinmode_in && IS_CLK_INVERTED_BIN;
    assign inmode_en_p = ceinmode_in && ~rstinmode_in && ~IS_CLK_INVERTED_BIN;
    assign d_en_n = ced_in && ~rstd_in && IS_CLK_INVERTED_BIN;
    assign d_en_p = ced_in && ~rstd_in && ~IS_CLK_INVERTED_BIN;

    assign clk_gsr_en_n = ~gsr_in && IS_CLK_INVERTED_BIN;
    assign clk_gsr_en_p = ~gsr_in && ~IS_CLK_INVERTED_BIN;
    assign clk_rsta_en_n = ~rsta_in && IS_CLK_INVERTED_BIN;
    assign clk_rsta_en_p = ~rsta_in && ~IS_CLK_INVERTED_BIN;
    assign clk_rstb_en_n = ~rstb_in && IS_CLK_INVERTED_BIN;
    assign clk_rstb_en_p = ~rstb_in && ~IS_CLK_INVERTED_BIN;
    assign clk_rstc_en_n = ~rstc_in && IS_CLK_INVERTED_BIN;
    assign clk_rstc_en_p = ~rstc_in && ~IS_CLK_INVERTED_BIN;
    assign clk_rstd_en_n = ~rstd_in && IS_CLK_INVERTED_BIN;
    assign clk_rstd_en_p = ~rstd_in && ~IS_CLK_INVERTED_BIN;
    assign clk_rstm_en_n = ~rstm_in && IS_CLK_INVERTED_BIN;
    assign clk_rstm_en_p = ~rstm_in && ~IS_CLK_INVERTED_BIN;
    assign clk_rstp_en_n = ~rstp_in && IS_CLK_INVERTED_BIN;
    assign clk_rstp_en_p = ~rstp_in && ~IS_CLK_INVERTED_BIN;
    assign clk_rstallcarryin_en_n = ~rstallcarryin_in && IS_CLK_INVERTED_BIN;
    assign clk_rstallcarryin_en_p = ~rstallcarryin_in && ~IS_CLK_INVERTED_BIN;
    assign clk_rstctrl_en_n = ~rstctrl_in && IS_CLK_INVERTED_BIN;
    assign clk_rstctrl_en_p = ~rstctrl_in && ~IS_CLK_INVERTED_BIN;
    assign clk_rstinmode_en_n = ~rstinmode_in && IS_CLK_INVERTED_BIN;
    assign clk_rstinmode_en_p = ~rstinmode_in && ~IS_CLK_INVERTED_BIN;
    assign clk_en_n = IS_CLK_INVERTED_BIN;
    assign clk_en_p = ~IS_CLK_INVERTED_BIN;
`endif

  specify
    (A *> ACOUT) = (0:0:0, 0:0:0);
    (A *> CARRYCASCOUT) = (0:0:0, 0:0:0);
    (A *> CARRYOUT) = (0:0:0, 0:0:0);
    (A *> MULTSIGNOUT) = (0:0:0, 0:0:0);
    (A *> OVERFLOW) = (0:0:0, 0:0:0);
    (A *> P) = (0:0:0, 0:0:0);
    (A *> PATTERNBDETECT) = (0:0:0, 0:0:0);
    (A *> PATTERNDETECT) = (0:0:0, 0:0:0);
    (A *> PCOUT) = (0:0:0, 0:0:0);
    (A *> UNDERFLOW) = (0:0:0, 0:0:0);
    (ACIN *> ACOUT) = (0:0:0, 0:0:0);
    (ACIN *> CARRYCASCOUT) = (0:0:0, 0:0:0);
    (ACIN *> CARRYOUT) = (0:0:0, 0:0:0);
    (ACIN *> MULTSIGNOUT) = (0:0:0, 0:0:0);
    (ACIN *> OVERFLOW) = (0:0:0, 0:0:0);
    (ACIN *> P) = (0:0:0, 0:0:0);
    (ACIN *> PATTERNBDETECT) = (0:0:0, 0:0:0);
    (ACIN *> PATTERNDETECT) = (0:0:0, 0:0:0);
    (ACIN *> PCOUT) = (0:0:0, 0:0:0);
    (ACIN *> UNDERFLOW) = (0:0:0, 0:0:0);
    (ALUMODE *> CARRYCASCOUT) = (0:0:0, 0:0:0);
    (ALUMODE *> CARRYOUT) = (0:0:0, 0:0:0);
    (ALUMODE *> MULTSIGNOUT) = (0:0:0, 0:0:0);
    (ALUMODE *> OVERFLOW) = (0:0:0, 0:0:0);
    (ALUMODE *> P) = (0:0:0, 0:0:0);
    (ALUMODE *> PATTERNBDETECT) = (0:0:0, 0:0:0);
    (ALUMODE *> PATTERNDETECT) = (0:0:0, 0:0:0);
    (ALUMODE *> PCOUT) = (0:0:0, 0:0:0);
    (ALUMODE *> UNDERFLOW) = (0:0:0, 0:0:0);
    (B *> BCOUT) = (0:0:0, 0:0:0);
    (B *> CARRYCASCOUT) = (0:0:0, 0:0:0);
    (B *> CARRYOUT) = (0:0:0, 0:0:0);
    (B *> MULTSIGNOUT) = (0:0:0, 0:0:0);
    (B *> OVERFLOW) = (0:0:0, 0:0:0);
    (B *> P) = (0:0:0, 0:0:0);
    (B *> PATTERNBDETECT) = (0:0:0, 0:0:0);
    (B *> PATTERNDETECT) = (0:0:0, 0:0:0);
    (B *> PCOUT) = (0:0:0, 0:0:0);
    (B *> UNDERFLOW) = (0:0:0, 0:0:0);
    (BCIN *> BCOUT) = (0:0:0, 0:0:0);
    (BCIN *> CARRYCASCOUT) = (0:0:0, 0:0:0);
    (BCIN *> CARRYOUT) = (0:0:0, 0:0:0);
    (BCIN *> MULTSIGNOUT) = (0:0:0, 0:0:0);
    (BCIN *> OVERFLOW) = (0:0:0, 0:0:0);
    (BCIN *> P) = (0:0:0, 0:0:0);
    (BCIN *> PATTERNBDETECT) = (0:0:0, 0:0:0);
    (BCIN *> PATTERNDETECT) = (0:0:0, 0:0:0);
    (BCIN *> PCOUT) = (0:0:0, 0:0:0);
    (BCIN *> UNDERFLOW) = (0:0:0, 0:0:0);
    (C *> CARRYCASCOUT) = (0:0:0, 0:0:0);
    (C *> CARRYOUT) = (0:0:0, 0:0:0);
    (C *> MULTSIGNOUT) = (0:0:0, 0:0:0);
    (C *> OVERFLOW) = (0:0:0, 0:0:0);
    (C *> P) = (0:0:0, 0:0:0);
    (C *> PATTERNBDETECT) = (0:0:0, 0:0:0);
    (C *> PATTERNDETECT) = (0:0:0, 0:0:0);
    (C *> PCOUT) = (0:0:0, 0:0:0);
    (C *> UNDERFLOW) = (0:0:0, 0:0:0);
    (CARRYCASCIN *> CARRYOUT) = (0:0:0, 0:0:0);
    (CARRYCASCIN *> P) = (0:0:0, 0:0:0);
    (CARRYCASCIN *> PCOUT) = (0:0:0, 0:0:0);
    (CARRYCASCIN => CARRYCASCOUT) = (0:0:0, 0:0:0);
    (CARRYCASCIN => MULTSIGNOUT) = (0:0:0, 0:0:0);
    (CARRYCASCIN => OVERFLOW) = (0:0:0, 0:0:0);
    (CARRYCASCIN => PATTERNBDETECT) = (0:0:0, 0:0:0);
    (CARRYCASCIN => PATTERNDETECT) = (0:0:0, 0:0:0);
    (CARRYCASCIN => UNDERFLOW) = (0:0:0, 0:0:0);
    (CARRYIN *> CARRYOUT) = (0:0:0, 0:0:0);
    (CARRYIN *> P) = (0:0:0, 0:0:0);
    (CARRYIN *> PCOUT) = (0:0:0, 0:0:0);
    (CARRYIN => CARRYCASCOUT) = (0:0:0, 0:0:0);
    (CARRYIN => MULTSIGNOUT) = (0:0:0, 0:0:0);
    (CARRYIN => OVERFLOW) = (0:0:0, 0:0:0);
    (CARRYIN => PATTERNBDETECT) = (0:0:0, 0:0:0);
    (CARRYIN => PATTERNDETECT) = (0:0:0, 0:0:0);
    (CARRYIN => UNDERFLOW) = (0:0:0, 0:0:0);
    (CARRYINSEL *> CARRYCASCOUT) = (0:0:0, 0:0:0);
    (CARRYINSEL *> CARRYOUT) = (0:0:0, 0:0:0);
    (CARRYINSEL *> MULTSIGNOUT) = (0:0:0, 0:0:0);
    (CARRYINSEL *> OVERFLOW) = (0:0:0, 0:0:0);
    (CARRYINSEL *> P) = (0:0:0, 0:0:0);
    (CARRYINSEL *> PATTERNBDETECT) = (0:0:0, 0:0:0);
    (CARRYINSEL *> PATTERNDETECT) = (0:0:0, 0:0:0);
    (CARRYINSEL *> PCOUT) = (0:0:0, 0:0:0);
    (CARRYINSEL *> UNDERFLOW) = (0:0:0, 0:0:0);
    (CLK *> ACOUT) = (100:100:100, 100:100:100);
    (CLK *> BCOUT) = (100:100:100, 100:100:100);
    (CLK *> CARRYOUT) = (100:100:100, 100:100:100);
    (CLK *> P) = (100:100:100, 100:100:100);
    (CLK *> PCOUT) = (100:100:100, 100:100:100);
    (CLK => CARRYCASCOUT) = (100:100:100, 100:100:100);
    (CLK => MULTSIGNOUT) = (100:100:100, 100:100:100);
    (CLK => OVERFLOW) = (100:100:100, 100:100:100);
    (CLK => PATTERNBDETECT) = (100:100:100, 100:100:100);
    (CLK => PATTERNDETECT) = (100:100:100, 100:100:100);
    (CLK => UNDERFLOW) = (100:100:100, 100:100:100);
    (D *> CARRYCASCOUT) = (0:0:0, 0:0:0);
    (D *> CARRYOUT) = (0:0:0, 0:0:0);
    (D *> MULTSIGNOUT) = (0:0:0, 0:0:0);
    (D *> OVERFLOW) = (0:0:0, 0:0:0);
    (D *> P) = (0:0:0, 0:0:0);
    (D *> PATTERNBDETECT) = (0:0:0, 0:0:0);
    (D *> PATTERNDETECT) = (0:0:0, 0:0:0);
    (D *> PCOUT) = (0:0:0, 0:0:0);
    (D *> UNDERFLOW) = (0:0:0, 0:0:0);
    (INMODE *> CARRYCASCOUT) = (0:0:0, 0:0:0);
    (INMODE *> CARRYOUT) = (0:0:0, 0:0:0);
    (INMODE *> MULTSIGNOUT) = (0:0:0, 0:0:0);
    (INMODE *> OVERFLOW) = (0:0:0, 0:0:0);
    (INMODE *> P) = (0:0:0, 0:0:0);
    (INMODE *> PATTERNBDETECT) = (0:0:0, 0:0:0);
    (INMODE *> PATTERNDETECT) = (0:0:0, 0:0:0);
    (INMODE *> PCOUT) = (0:0:0, 0:0:0);
    (INMODE *> UNDERFLOW) = (0:0:0, 0:0:0);
    (MULTSIGNIN *> CARRYOUT) = (0:0:0, 0:0:0);
    (MULTSIGNIN *> P) = (0:0:0, 0:0:0);
    (MULTSIGNIN *> PCOUT) = (0:0:0, 0:0:0);
    (MULTSIGNIN => CARRYCASCOUT) = (0:0:0, 0:0:0);
    (MULTSIGNIN => MULTSIGNOUT) = (0:0:0, 0:0:0);
    (MULTSIGNIN => OVERFLOW) = (0:0:0, 0:0:0);
    (MULTSIGNIN => PATTERNBDETECT) = (0:0:0, 0:0:0);
    (MULTSIGNIN => PATTERNDETECT) = (0:0:0, 0:0:0);
    (MULTSIGNIN => UNDERFLOW) = (0:0:0, 0:0:0);
    (OPMODE *> CARRYCASCOUT) = (0:0:0, 0:0:0);
    (OPMODE *> CARRYOUT) = (0:0:0, 0:0:0);
    (OPMODE *> MULTSIGNOUT) = (0:0:0, 0:0:0);
    (OPMODE *> OVERFLOW) = (0:0:0, 0:0:0);
    (OPMODE *> P) = (0:0:0, 0:0:0);
    (OPMODE *> PATTERNBDETECT) = (0:0:0, 0:0:0);
    (OPMODE *> PATTERNDETECT) = (0:0:0, 0:0:0);
    (OPMODE *> PCOUT) = (0:0:0, 0:0:0);
    (OPMODE *> UNDERFLOW) = (0:0:0, 0:0:0);
    (PCIN *> CARRYCASCOUT) = (0:0:0, 0:0:0);
    (PCIN *> CARRYOUT) = (0:0:0, 0:0:0);
    (PCIN *> MULTSIGNOUT) = (0:0:0, 0:0:0);
    (PCIN *> OVERFLOW) = (0:0:0, 0:0:0);
    (PCIN *> P) = (0:0:0, 0:0:0);
    (PCIN *> PATTERNBDETECT) = (0:0:0, 0:0:0);
    (PCIN *> PATTERNDETECT) = (0:0:0, 0:0:0);
    (PCIN *> PCOUT) = (0:0:0, 0:0:0);
    (PCIN *> UNDERFLOW) = (0:0:0, 0:0:0);
`ifdef XIL_TIMING
    $period (negedge CLK, 0:0:0, notifier);
    $period (posedge CLK, 0:0:0, notifier);
    $setuphold (negedge CLK, negedge A, 0:0:0, 0:0:0, notifier,a_en_n,a_en_n, clk_dly, a_dly);
    $setuphold (negedge CLK, negedge ACIN, 0:0:0, 0:0:0, notifier,acin_en_n,acin_en_n, clk_dly, acin_dly);
    $setuphold (negedge CLK, negedge ALUMODE, 0:0:0, 0:0:0, notifier,clk_en_n,clk_en_n, clk_dly, alumode_dly);
    $setuphold (negedge CLK, negedge B, 0:0:0, 0:0:0, notifier,b_en_n,b_en_n, clk_dly, b_dly);
    $setuphold (negedge CLK, negedge BCIN, 0:0:0, 0:0:0, notifier,bcin_en_n,bcin_en_n, clk_dly, bcin_dly);
    $setuphold (negedge CLK, negedge C, 0:0:0, 0:0:0, notifier,c_en_n,c_en_n, clk_dly, c_dly);
    $setuphold (negedge CLK, negedge CARRYCASCIN, 0:0:0, 0:0:0, notifier,clk_en_n,clk_en_n, clk_dly, carrycascin_dly);
    $setuphold (negedge CLK, negedge CARRYIN, 0:0:0, 0:0:0, notifier,carryin_en_n,carryin_en_n, clk_dly, carryin_dly);
    $setuphold (negedge CLK, negedge CARRYINSEL, 0:0:0, 0:0:0, notifier,carryinsel_en_n,carryinsel_en_n, clk_dly, carryinsel_dly);
    $setuphold (negedge CLK, negedge CEA1, 0:0:0, 0:0:0, notifier,clk_rsta_en_n,clk_rsta_en_n, clk_dly, cea1_dly);
    $setuphold (negedge CLK, negedge CEA2, 0:0:0, 0:0:0, notifier,clk_rsta_en_n,clk_rsta_en_n, clk_dly, cea2_dly);
    $setuphold (negedge CLK, negedge CEAD, 0:0:0, 0:0:0, notifier,clk_rstd_en_n,clk_rstd_en_n, clk_dly, cead_dly);
    $setuphold (negedge CLK, negedge CEALUMODE, 0:0:0, 0:0:0, notifier,clk_en_n,clk_en_n, clk_dly, cealumode_dly);
    $setuphold (negedge CLK, negedge CEB1, 0:0:0, 0:0:0, notifier,clk_rstb_en_n,clk_rstb_en_n, clk_dly, ceb1_dly);
    $setuphold (negedge CLK, negedge CEB2, 0:0:0, 0:0:0, notifier,clk_rstb_en_n,clk_rstb_en_n, clk_dly, ceb2_dly);
    $setuphold (negedge CLK, negedge CEC, 0:0:0, 0:0:0, notifier,clk_rstc_en_n,clk_rstc_en_n, clk_dly, cec_dly);
    $setuphold (negedge CLK, negedge CECARRYIN, 0:0:0, 0:0:0, notifier,clk_rstallcarryin_en_n,clk_rstallcarryin_en_n, clk_dly, cecarryin_dly);
    $setuphold (negedge CLK, negedge CECTRL, 0:0:0, 0:0:0, notifier,clk_rstctrl_en_n,clk_rstctrl_en_n, clk_dly, cectrl_dly);
    $setuphold (negedge CLK, negedge CED, 0:0:0, 0:0:0, notifier,clk_rstd_en_n,clk_rstd_en_n, clk_dly, ced_dly);
    $setuphold (negedge CLK, negedge CEINMODE, 0:0:0, 0:0:0, notifier,clk_rstinmode_en_n,clk_rstinmode_en_n, clk_dly, ceinmode_dly);
    $setuphold (negedge CLK, negedge CEM, 0:0:0, 0:0:0, notifier,clk_rstm_en_n,clk_rstm_en_n, clk_dly, cem_dly);
    $setuphold (negedge CLK, negedge CEP, 0:0:0, 0:0:0, notifier,clk_rstp_en_n,clk_rstp_en_n, clk_dly, cep_dly);
    $setuphold (negedge CLK, negedge D, 0:0:0, 0:0:0, notifier,d_en_n,d_en_n, clk_dly, d_dly);
    $setuphold (negedge CLK, negedge INMODE, 0:0:0, 0:0:0, notifier,inmode_en_n,inmode_en_n, clk_dly, inmode_dly);
    $setuphold (negedge CLK, negedge MULTSIGNIN, 0:0:0, 0:0:0, notifier,clk_en_n,clk_en_n, clk_dly, multsignin_dly);
    $setuphold (negedge CLK, negedge OPMODE, 0:0:0, 0:0:0, notifier,opmode_en_n,opmode_en_n, clk_dly, opmode_dly);
    $setuphold (negedge CLK, negedge PCIN, 0:0:0, 0:0:0, notifier,pcin_en_n,pcin_en_n, clk_dly, pcin_dly);
    $setuphold (negedge CLK, negedge RSTA, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rsta_dly);
    $setuphold (negedge CLK, negedge RSTALLCARRYIN, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstallcarryin_dly);
    $setuphold (negedge CLK, negedge RSTALUMODE, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstalumode_dly);
    $setuphold (negedge CLK, negedge RSTB, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstb_dly);
    $setuphold (negedge CLK, negedge RSTC, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstc_dly);
    $setuphold (negedge CLK, negedge RSTCTRL, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstctrl_dly);
    $setuphold (negedge CLK, negedge RSTD, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstd_dly);
    $setuphold (negedge CLK, negedge RSTINMODE, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstinmode_dly);
    $setuphold (negedge CLK, negedge RSTM, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstm_dly);
    $setuphold (negedge CLK, negedge RSTP, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstp_dly);
    $setuphold (negedge CLK, posedge A, 0:0:0, 0:0:0, notifier,a_en_n,a_en_n, clk_dly, a_dly);
    $setuphold (negedge CLK, posedge ACIN, 0:0:0, 0:0:0, notifier,acin_en_n,acin_en_n, clk_dly, acin_dly);
    $setuphold (negedge CLK, posedge ALUMODE, 0:0:0, 0:0:0, notifier,clk_en_n,clk_en_n, clk_dly, alumode_dly);
    $setuphold (negedge CLK, posedge B, 0:0:0, 0:0:0, notifier,b_en_n,b_en_n, clk_dly, b_dly );
    $setuphold (negedge CLK, posedge BCIN, 0:0:0, 0:0:0, notifier,bcin_en_n,bcin_en_n, clk_dly, bcin_dly);
    $setuphold (negedge CLK, posedge C, 0:0:0, 0:0:0, notifier,c_en_n,c_en_n, clk_dly, c_dly);
    $setuphold (negedge CLK, posedge CARRYCASCIN, 0:0:0, 0:0:0, notifier,clk_en_n,clk_en_n, clk_dly, carrycascin_dly);
    $setuphold (negedge CLK, posedge CARRYIN, 0:0:0, 0:0:0, notifier,carryin_en_n,carryin_en_n, clk_dly, carryin_dly);
    $setuphold (negedge CLK, posedge CARRYINSEL, 0:0:0, 0:0:0, notifier,carryinsel_en_n,carryinsel_en_n, clk_dly, carryinsel_dly);
    $setuphold (negedge CLK, posedge CEA1, 0:0:0, 0:0:0, notifier,clk_rsta_en_n,clk_rsta_en_n, clk_dly, cea1_dly);
    $setuphold (negedge CLK, posedge CEA2, 0:0:0, 0:0:0, notifier,clk_rsta_en_n,clk_rsta_en_n, clk_dly, cea2_dly);
    $setuphold (negedge CLK, posedge CEAD, 0:0:0, 0:0:0, notifier,clk_rstd_en_n,clk_rstd_en_n, clk_dly, cead_dly);
    $setuphold (negedge CLK, posedge CEALUMODE, 0:0:0, 0:0:0, notifier,clk_en_n,clk_en_n, clk_dly, cealumode_dly);
    $setuphold (negedge CLK, posedge CEB1, 0:0:0, 0:0:0, notifier,clk_rstb_en_n,clk_rstb_en_n, clk_dly, ceb1_dly);
    $setuphold (negedge CLK, posedge CEB2, 0:0:0, 0:0:0, notifier,clk_rstb_en_n,clk_rstb_en_n, clk_dly, ceb2_dly);
    $setuphold (negedge CLK, posedge CEC, 0:0:0, 0:0:0, notifier,clk_rstc_en_n,clk_rstc_en_n, clk_dly, cec_dly);
    $setuphold (negedge CLK, posedge CECARRYIN, 0:0:0, 0:0:0, notifier,clk_rstallcarryin_en_n,clk_rstallcarryin_en_n, clk_dly, cecarryin_dly);
    $setuphold (negedge CLK, posedge CECTRL, 0:0:0, 0:0:0, notifier,clk_rstctrl_en_n,clk_rstctrl_en_n, clk_dly, cectrl_dly);
    $setuphold (negedge CLK, posedge CED, 0:0:0, 0:0:0, notifier,clk_rstd_en_n,clk_rstd_en_n, clk_dly, ced_dly);
    $setuphold (negedge CLK, posedge CEINMODE, 0:0:0, 0:0:0, notifier,clk_rstinmode_en_n,clk_rstinmode_en_n, clk_dly, ceinmode_dly);
    $setuphold (negedge CLK, posedge CEM, 0:0:0, 0:0:0, notifier,clk_rstm_en_n,clk_rstm_en_n, clk_dly, cem_dly);
    $setuphold (negedge CLK, posedge CEP, 0:0:0, 0:0:0, notifier,clk_rstp_en_n,clk_rstp_en_n, clk_dly, cep_dly);
    $setuphold (negedge CLK, posedge D, 0:0:0, 0:0:0, notifier,d_en_n,d_en_n, clk_dly, d_dly);
    $setuphold (negedge CLK, posedge INMODE, 0:0:0, 0:0:0, notifier,inmode_en_n,inmode_en_n, clk_dly, inmode_dly);
    $setuphold (negedge CLK, posedge MULTSIGNIN, 0:0:0, 0:0:0, notifier,clk_en_n,clk_en_n, clk_dly, multsignin_dly);
    $setuphold (negedge CLK, posedge OPMODE, 0:0:0, 0:0:0, notifier,opmode_en_n,opmode_en_n, clk_dly, opmode_dly);
    $setuphold (negedge CLK, posedge PCIN, 0:0:0, 0:0:0, notifier,pcin_en_n,pcin_en_n, clk_dly, pcin_dly);
    $setuphold (negedge CLK, posedge RSTA, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rsta_dly);
    $setuphold (negedge CLK, posedge RSTALLCARRYIN, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstallcarryin_dly);
    $setuphold (negedge CLK, posedge RSTALUMODE, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstalumode_dly);
    $setuphold (negedge CLK, posedge RSTB, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstb_dly);
    $setuphold (negedge CLK, posedge RSTC, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstc_dly);
    $setuphold (negedge CLK, posedge RSTCTRL, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstctrl_dly);
    $setuphold (negedge CLK, posedge RSTD, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstd_dly);
    $setuphold (negedge CLK, posedge RSTINMODE, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstinmode_dly);
    $setuphold (negedge CLK, posedge RSTM, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstm_dly);
    $setuphold (negedge CLK, posedge RSTP, 0:0:0, 0:0:0, notifier,clk_gsr_en_n,clk_gsr_en_n, clk_dly, rstp_dly);
    $setuphold (posedge CLK, negedge A, 0:0:0, 0:0:0, notifier,a_en_p,a_en_p, clk_dly, a_dly);
    $setuphold (posedge CLK, negedge ACIN, 0:0:0, 0:0:0, notifier,acin_en_p,acin_en_p, clk_dly, acin_dly);
    $setuphold (posedge CLK, negedge ALUMODE, 0:0:0, 0:0:0, notifier,clk_en_p,clk_en_p, clk_dly, alumode_dly);
    $setuphold (posedge CLK, negedge B, 0:0:0, 0:0:0, notifier,b_en_p,b_en_p, clk_dly, b_dly);
    $setuphold (posedge CLK, negedge BCIN, 0:0:0, 0:0:0, notifier,bcin_en_p,bcin_en_p, clk_dly, bcin_dly);
    $setuphold (posedge CLK, negedge C, 0:0:0, 0:0:0, notifier,c_en_p,c_en_p, clk_dly, c_dly);
    $setuphold (posedge CLK, negedge CARRYCASCIN, 0:0:0, 0:0:0, notifier,clk_en_p,clk_en_p, clk_dly, carrycascin_dly);
    $setuphold (posedge CLK, negedge CARRYIN, 0:0:0, 0:0:0, notifier,carryin_en_p,carryin_en_p, clk_dly, carryin_dly);
    $setuphold (posedge CLK, negedge CARRYINSEL, 0:0:0, 0:0:0, notifier,carryinsel_en_p,carryinsel_en_p, clk_dly, carryinsel_dly);
    $setuphold (posedge CLK, negedge CEA1, 0:0:0, 0:0:0, notifier,clk_rsta_en_p,clk_rsta_en_p, clk_dly, cea1_dly);
    $setuphold (posedge CLK, negedge CEA2, 0:0:0, 0:0:0, notifier,clk_rsta_en_p,clk_rsta_en_p, clk_dly, cea2_dly);
    $setuphold (posedge CLK, negedge CEAD, 0:0:0, 0:0:0, notifier,clk_rstd_en_p,clk_rstd_en_p, clk_dly, cead_dly);
    $setuphold (posedge CLK, negedge CEALUMODE, 0:0:0, 0:0:0, notifier,clk_en_p,clk_en_p, clk_dly, cealumode_dly);
    $setuphold (posedge CLK, negedge CEB1, 0:0:0, 0:0:0, notifier,clk_rstb_en_p,clk_rstb_en_p, clk_dly, ceb1_dly);
    $setuphold (posedge CLK, negedge CEB2, 0:0:0, 0:0:0, notifier,clk_rstb_en_p,clk_rstb_en_p, clk_dly, ceb2_dly);
    $setuphold (posedge CLK, negedge CEC, 0:0:0, 0:0:0, notifier,clk_rstc_en_p,clk_rstc_en_p, clk_dly, cec_dly);
    $setuphold (posedge CLK, negedge CECARRYIN, 0:0:0, 0:0:0, notifier,clk_rstallcarryin_en_p,clk_rstallcarryin_en_p, clk_dly, cecarryin_dly);
    $setuphold (posedge CLK, negedge CECTRL, 0:0:0, 0:0:0, notifier,clk_rstctrl_en_p,clk_rstctrl_en_p, clk_dly, cectrl_dly);
    $setuphold (posedge CLK, negedge CED, 0:0:0, 0:0:0, notifier,clk_rstd_en_p,clk_rstd_en_p, clk_dly, ced_dly);
    $setuphold (posedge CLK, negedge CEINMODE, 0:0:0, 0:0:0, notifier,clk_rstinmode_en_p,clk_rstinmode_en_p, clk_dly, ceinmode_dly);
    $setuphold (posedge CLK, negedge CEM, 0:0:0, 0:0:0, notifier,clk_rstm_en_p,clk_rstm_en_p, clk_dly, cem_dly);
    $setuphold (posedge CLK, negedge CEP, 0:0:0, 0:0:0, notifier,clk_rstp_en_p,clk_rstp_en_p, clk_dly, cep_dly);
    $setuphold (posedge CLK, negedge D, 0:0:0, 0:0:0, notifier,d_en_p,d_en_p, clk_dly, d_dly);
    $setuphold (posedge CLK, negedge INMODE, 0:0:0, 0:0:0, notifier,inmode_en_p,inmode_en_p, clk_dly, inmode_dly);
    $setuphold (posedge CLK, negedge MULTSIGNIN, 0:0:0, 0:0:0, notifier,clk_en_p,clk_en_p, clk_dly, multsignin_dly);
    $setuphold (posedge CLK, negedge OPMODE, 0:0:0, 0:0:0, notifier,opmode_en_p,opmode_en_p, clk_dly, opmode_dly);
    $setuphold (posedge CLK, negedge PCIN, 0:0:0, 0:0:0, notifier,pcin_en_p,pcin_en_p, clk_dly, pcin_dly);
    $setuphold (posedge CLK, negedge RSTA, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rsta_dly);
    $setuphold (posedge CLK, negedge RSTALLCARRYIN, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstallcarryin_dly);
    $setuphold (posedge CLK, negedge RSTALUMODE, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstalumode_dly);
    $setuphold (posedge CLK, negedge RSTB, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstb_dly);
    $setuphold (posedge CLK, negedge RSTC, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstc_dly);
    $setuphold (posedge CLK, negedge RSTCTRL, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstctrl_dly);
    $setuphold (posedge CLK, negedge RSTD, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstd_dly);
    $setuphold (posedge CLK, negedge RSTINMODE, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstinmode_dly);
    $setuphold (posedge CLK, negedge RSTM, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstm_dly);
    $setuphold (posedge CLK, negedge RSTP, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstp_dly);
    $setuphold (posedge CLK, posedge A, 0:0:0, 0:0:0, notifier,a_en_p,a_en_p, clk_dly, a_dly);
    $setuphold (posedge CLK, posedge ACIN, 0:0:0, 0:0:0, notifier,acin_en_p,acin_en_p, clk_dly, acin_dly);
    $setuphold (posedge CLK, posedge ALUMODE, 0:0:0, 0:0:0, notifier,clk_en_p,clk_en_p, clk_dly, alumode_dly);
    $setuphold (posedge CLK, posedge B, 0:0:0, 0:0:0, notifier,b_en_p,b_en_p, clk_dly, b_dly );
    $setuphold (posedge CLK, posedge BCIN, 0:0:0, 0:0:0, notifier,bcin_en_p,bcin_en_p, clk_dly, bcin_dly);
    $setuphold (posedge CLK, posedge C, 0:0:0, 0:0:0, notifier,c_en_p,c_en_p, clk_dly, c_dly);
    $setuphold (posedge CLK, posedge CARRYCASCIN, 0:0:0, 0:0:0, notifier,clk_en_p,clk_en_p, clk_dly, carrycascin_dly);
    $setuphold (posedge CLK, posedge CARRYIN, 0:0:0, 0:0:0, notifier,carryin_en_p,carryin_en_p, clk_dly, carryin_dly);
    $setuphold (posedge CLK, posedge CARRYINSEL, 0:0:0, 0:0:0, notifier,carryinsel_en_p,carryinsel_en_p, clk_dly, carryinsel_dly);
    $setuphold (posedge CLK, posedge CEA1, 0:0:0, 0:0:0, notifier,clk_rsta_en_p,clk_rsta_en_p, clk_dly, cea1_dly);
    $setuphold (posedge CLK, posedge CEA2, 0:0:0, 0:0:0, notifier,clk_rsta_en_p,clk_rsta_en_p, clk_dly, cea2_dly);
    $setuphold (posedge CLK, posedge CEAD, 0:0:0, 0:0:0, notifier,clk_rstd_en_p,clk_rstd_en_p, clk_dly, cead_dly);
    $setuphold (posedge CLK, posedge CEALUMODE, 0:0:0, 0:0:0, notifier,clk_en_p,clk_en_p, clk_dly, cealumode_dly);
    $setuphold (posedge CLK, posedge CEB1, 0:0:0, 0:0:0, notifier,clk_rstb_en_p,clk_rstb_en_p, clk_dly, ceb1_dly);
    $setuphold (posedge CLK, posedge CEB2, 0:0:0, 0:0:0, notifier,clk_rstb_en_p,clk_rstb_en_p, clk_dly, ceb2_dly);
    $setuphold (posedge CLK, posedge CEC, 0:0:0, 0:0:0, notifier,clk_rstc_en_p,clk_rstc_en_p, clk_dly, cec_dly);
    $setuphold (posedge CLK, posedge CECARRYIN, 0:0:0, 0:0:0, notifier,clk_rstallcarryin_en_p,clk_rstallcarryin_en_p, clk_dly, cecarryin_dly);
    $setuphold (posedge CLK, posedge CECTRL, 0:0:0, 0:0:0, notifier,clk_rstctrl_en_p,clk_rstctrl_en_p, clk_dly, cectrl_dly);
    $setuphold (posedge CLK, posedge CED, 0:0:0, 0:0:0, notifier,clk_rstd_en_p,clk_rstd_en_p, clk_dly, ced_dly);
    $setuphold (posedge CLK, posedge CEINMODE, 0:0:0, 0:0:0, notifier,clk_rstinmode_en_p,clk_rstinmode_en_p, clk_dly, ceinmode_dly);
    $setuphold (posedge CLK, posedge CEM, 0:0:0, 0:0:0, notifier,clk_rstm_en_p,clk_rstm_en_p, clk_dly, cem_dly);
    $setuphold (posedge CLK, posedge CEP, 0:0:0, 0:0:0, notifier,clk_rstp_en_p,clk_rstp_en_p, clk_dly, cep_dly);
    $setuphold (posedge CLK, posedge D, 0:0:0, 0:0:0, notifier,d_en_p,d_en_p, clk_dly, d_dly);
    $setuphold (posedge CLK, posedge INMODE, 0:0:0, 0:0:0, notifier,inmode_en_p,inmode_en_p, clk_dly, inmode_dly);
    $setuphold (posedge CLK, posedge MULTSIGNIN, 0:0:0, 0:0:0, notifier,clk_en_p,clk_en_p, clk_dly, multsignin_dly);
    $setuphold (posedge CLK, posedge OPMODE, 0:0:0, 0:0:0, notifier,opmode_en_p,opmode_en_p, clk_dly, opmode_dly);
    $setuphold (posedge CLK, posedge PCIN, 0:0:0, 0:0:0, notifier,pcin_en_p,pcin_en_p, clk_dly, pcin_dly);
    $setuphold (posedge CLK, posedge RSTA, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rsta_dly);
    $setuphold (posedge CLK, posedge RSTALLCARRYIN, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstallcarryin_dly);
    $setuphold (posedge CLK, posedge RSTALUMODE, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstalumode_dly);
    $setuphold (posedge CLK, posedge RSTB, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstb_dly);
    $setuphold (posedge CLK, posedge RSTC, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstc_dly);
    $setuphold (posedge CLK, posedge RSTCTRL, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstctrl_dly);
    $setuphold (posedge CLK, posedge RSTD, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstd_dly);
    $setuphold (posedge CLK, posedge RSTINMODE, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstinmode_dly);
    $setuphold (posedge CLK, posedge RSTM, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstm_dly);
    $setuphold (posedge CLK, posedge RSTP, 0:0:0, 0:0:0, notifier,clk_gsr_en_p,clk_gsr_en_p, clk_dly, rstp_dly);
    $width (negedge CLK, 0:0:0, 0, notifier);
    $width (posedge CLK, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
