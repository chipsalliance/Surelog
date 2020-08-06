///////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2010 Xilinx, Inc.
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
// \   \   \/     Version : 10.1
//  \   \         Description : Xilinx Functional Simulation Library Component
//  /   /                  Jtag TAP Controler for VIRTEX7
// /___/   /\     Filename : JTAG_SIME2.v
// \   \  /  \    Timestamp : Mon May 17 17:10:29 PDT 2010
//  \___\/\___\
//
// Revision:
//    05/17/10 - Initial version.
//    11/30/11 - 632642 - Updated supported devices and corresponding IDCODES.
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//    07/05/12 - Updated the simulation model (CR 667100).
//    07/23/12 - Fixed IRLengthMax (CR 669116).
//    04/07/15 - Added negedge to RESET, RUNTEST, UPDATE and TDO (CR 857726).
// End Revision

`timescale 1 ps/1 ps

`celldefine

module JTAG_SIME2( TDO, TCK, TDI, TMS);


  output TDO;

  input TCK, TDI, TMS;
   
  reg TDO;
  reg notifier;


  parameter PART_NAME = "7K325T";

`ifdef XIL_TIMING
    parameter LOC = "UNPLACED";
`endif //  `ifdef XIL_TIMING
    
  localparam       TestLogicReset       = 4'h0,
                   RunTestIdle          = 4'h1,
                   SelectDRScan         = 4'h2,
                   CaptureDR            = 4'h3,
                   ShiftDR              = 4'h4,
                   Exit1DR              = 4'h5,
                   PauseDR              = 4'h6,
                   Exit2DR              = 4'h7,
                   UpdateDR             = 4'h8,
                   SelectIRScan         = 4'h9,
                   CaptureIR            = 4'ha,
                   ShiftIR              = 4'hb,
                   Exit1IR              = 4'hc,
                   PauseIR              = 4'hd,
                   Exit2IR              = 4'he,
                   UpdateIR             = 4'hf;

   localparam DELAY_SIG = 1;
   
   reg TRST = 0;

   reg [3:0]    CurrentState = TestLogicReset;
   reg [14*8:0] jtag_state_name = "TestLogicReset";
   reg [14*8:0] jtag_instruction_name = "IDCODE";


//-----------------  Virtex4 Specific Constants ---------
//  localparam IRLengthMax = 10;
    localparam IRLengthMax = 24;
  localparam IDLength    = 32;

  reg [IRLengthMax-1:0] IR_CAPTURE_VAL  = 24'b010001010001010001010001,
                      BYPASS_INSTR      = 24'b111111111111111111111111,
                      IDCODE_INSTR      = 24'b001001001001001001001001,
                      USER1_INSTR       = 24'b000010100100100100100100,
                      USER2_INSTR       = 24'b000011100100100100100100,
                      USER3_INSTR       = 24'b100010100100100100100100,
                      USER4_INSTR       = 24'b100011100100100100100100;

//  localparam IRLength = 10;
  localparam IRLength = ( 
        (PART_NAME   == "XCKU3P")       || (PART_NAME   == "xcku3p")     ||
        (PART_NAME   == "XCKU9P")       || (PART_NAME   == "xcku9p")     ||
        (PART_NAME   == "XCKU11P")      || (PART_NAME   == "xcku11p")    ||
        (PART_NAME   == "XCKU13EG")     || (PART_NAME   == "xcku13eg")   ||
        (PART_NAME   == "XCKU15P")      || (PART_NAME   == "xcku15p")    ||
        (PART_NAME   == "XCKU5P")       || (PART_NAME   == "xcku5p")     ||
        (PART_NAME   == "XCVU3P")       || (PART_NAME   == "xcvu3p")     ||
        (PART_NAME   == "KU025")        || (PART_NAME   == "ku025")      || 
        (PART_NAME   == "KU035")        || (PART_NAME   == "ku035")      || 
        (PART_NAME   == "KU040")        || (PART_NAME   == "ku040")      || 
        (PART_NAME   == "KU060")        || (PART_NAME   == "ku060")      || 
        (PART_NAME   == "KU095")        || (PART_NAME   == "ku095")      || 
        (PART_NAME   == "VU065")        || (PART_NAME   == "vu065")      || 
        (PART_NAME   == "VU080")        || (PART_NAME   == "vu080")      || 
        (PART_NAME   == "VU095")        || (PART_NAME   == "vu095")      || 
        (PART_NAME   == "7A15T")        || (PART_NAME   == "7a15t")      || 
        (PART_NAME   == "7A25T")        || (PART_NAME   == "7a25t")      || 
        (PART_NAME   == "7S15")         || (PART_NAME   == "7s15")       || 
        (PART_NAME   == "7S100")        || (PART_NAME   == "7s100")      || 
        (PART_NAME   == "7A35T")        || (PART_NAME   == "7a35t")      || 
        (PART_NAME   == "7A50T")        || (PART_NAME   == "7a50t")      || 
        (PART_NAME   == "7A75T")        || (PART_NAME   == "7a75t")      || 
        (PART_NAME   == "7A100T")       || (PART_NAME   == "7a100t")     || 
        (PART_NAME   == "7A200T")       || (PART_NAME   == "7a200t")     || 
        (PART_NAME   == "7K70T")        || (PART_NAME   == "7k70t")      || 
        (PART_NAME   == "7K160T")       || (PART_NAME   == "7k160t")     || 
        (PART_NAME   == "7K325T")       || (PART_NAME   == "7k325t")     || 
        (PART_NAME   == "7K355T")       || (PART_NAME   == "7k355t")     || 
        (PART_NAME   == "7K410T")       || (PART_NAME   == "7k410t")     || 
        (PART_NAME   == "7K420T")       || (PART_NAME   == "7k420t")     || 
        (PART_NAME   == "7K480T")       || (PART_NAME   == "7k480t")     || 
        (PART_NAME   == "7V585T")       || (PART_NAME   == "7v585t"))     ?      6 : (
        (PART_NAME   == "XCZU9EG")      || (PART_NAME   == "xczu9eg")    ||
        (PART_NAME   == "XCVU5P")       || (PART_NAME   == "xcvu5p")     ||
        (PART_NAME   == "XCVU7P")       || (PART_NAME   == "xcvu7p")     ||
        (PART_NAME   == "KU085")        || (PART_NAME   == "ku085")      || 
        (PART_NAME   == "KU115")        || (PART_NAME   == "ku115")      ||
        (PART_NAME   == "VU125")        || (PART_NAME   == "vu125"))      ?      12 : (
        (PART_NAME   == "XCZU3EG")      || (PART_NAME   == "xczu3eg")    ||
        (PART_NAME   == "XCZU4EG")      || (PART_NAME   == "xczu4eg")    ||
        (PART_NAME   == "XCZU5EG")      || (PART_NAME   == "xczu5eg")    ||
        (PART_NAME   == "XCZU7EG")      || (PART_NAME   == "xczu7eg")    ||
        (PART_NAME   == "XCZU2CG")      || (PART_NAME   == "xczu2cg")    ||
        (PART_NAME   == "XCZU3CG")      || (PART_NAME   == "xczu3cg")    ||
        (PART_NAME   == "XCZU4CG")      || (PART_NAME   == "xczu4cg")    ||
        (PART_NAME   == "XCZU5CG")      || (PART_NAME   == "xczu5cg")    ||
        (PART_NAME   == "XCZU6CG")      || (PART_NAME   == "xczu6cg")    ||
        (PART_NAME   == "XCZU7CG")      || (PART_NAME   == "xczu7cg")    ||
        (PART_NAME   == "XCZU9CG")      || (PART_NAME   == "xczu9cg")    ||
        (PART_NAME   == "XCZU5EV")      || (PART_NAME   == "xczu5ev")    ||
        (PART_NAME   == "XCZU11EG")     || (PART_NAME   == "xczu11eg")   ||
        (PART_NAME   == "XCZU15EG")     || (PART_NAME   == "xczu15eg")   ||
        (PART_NAME   == "XCZU19EG")     || (PART_NAME   == "xczu19eg")   ||
        (PART_NAME   == "XCZU7EV")      || (PART_NAME   == "xczu7ev")    ||
        (PART_NAME   == "XCZU2EG")      || (PART_NAME   == "xczu2eg")    ||
        (PART_NAME   == "XCZU4EV")      || (PART_NAME   == "xczu4ev")    ||
        (PART_NAME   == "XCZU6EG")      || (PART_NAME   == "xczu6eg")    ||
        (PART_NAME   == "XCZU17EG")     || (PART_NAME   == "xczu17eg"))   ?      16 : ( 
        (PART_NAME   == "XCVU13P")      || (PART_NAME   == "xcvu13p")    ||
        (PART_NAME   == "7V2000T")      || (PART_NAME   == "7v2000t"))    ?      24 : ( 
        (PART_NAME   == "7VH580T")      || (PART_NAME   == "7vh580t"))    ?      22 : ( 
        (PART_NAME   == "7VH870T")      || (PART_NAME   == "7vh870t"))    ?      38 : ( 
        (PART_NAME   == "7VX330T")      || (PART_NAME   == "7vx330t")    || 
        (PART_NAME   == "7VX415T")      || (PART_NAME   == "7vx415t")    || 
        (PART_NAME   == "7VX485T")      || (PART_NAME   == "7vx485t")    || 
        (PART_NAME   == "7VX550T")      || (PART_NAME   == "7vx550t")    || 
        (PART_NAME   == "7VX690T")      || (PART_NAME   == "7vx690t")    || 
        (PART_NAME   == "7VX980T")      || (PART_NAME   == "7vx980t"))    ?      6 : ( 
        (PART_NAME   == "7VX1140T")     || (PART_NAME   == "7vx1140t"))   ?      24 : ( 
        (PART_NAME   == "7Z010")        || (PART_NAME   == "7z010")      || 
        (PART_NAME   == "7Z015")        || (PART_NAME   == "7z015")      || 
        (PART_NAME   == "7Z020")        || (PART_NAME   == "7z020")      || 
        (PART_NAME   == "7Z030")        || (PART_NAME   == "7z030")      || 
        (PART_NAME   == "7Z035")        || (PART_NAME   == "7z035")      || 
        (PART_NAME   == "7Z045")        || (PART_NAME   == "7z045")      || 
        (PART_NAME   == "7Z007S")       || (PART_NAME   == "7z007s")     || 
        (PART_NAME   == "7Z012S")       || (PART_NAME   == "7z012s")     || 
        (PART_NAME   == "7Z014S")       || (PART_NAME   == "7z014s")     || 
        (PART_NAME   == "7Z100")        || (PART_NAME   == "7z100"))      ?      6 : ( 
        (PART_NAME   == "XCVU9P")       || (PART_NAME   == "xcvu9p")     ||
        (PART_NAME   == "XCVU11P")      || (PART_NAME   == "xcvu11p")    ||
        (PART_NAME   == "VU160")        || (PART_NAME   == "vu160")      || 
        (PART_NAME   == "VU190")        || (PART_NAME   == "vu190")      || 
        (PART_NAME   == "VU440")        || (PART_NAME   == "vu440"))      ?      18 : 24 ; 
//----------------- local reg  -------------------------------
  reg CaptureDR_sig = 0, RESET_sig = 0, ShiftDR_sig = 0, UpdateDR_sig = 0; 

  reg ClkIR_active = 0, ClkIR_sig = 0, ClkID_sig = 0; 

  reg ShiftIR_sig, UpdateIR_sig, ClkUpdateIR_sig; 
  
  reg [IRLength-1:0] IRcontent_sig;

  reg [IDLength-1:0] IDCODEval_sig;

  reg  BypassReg = 0, BYPASS_sig = 0, IDCODE_sig = 0, 
       USER1_sig = 0, USER2_sig = 0,
       USER3_sig = 0, USER4_sig = 0;

  reg TDO_latch;

  reg Tlrst_sig = 1; 
  reg TlrstN_sig = 1; 

  reg IRegLastBit_sig = 0, IDregLastBit_sig = 0;

  reg Rti_sig = 0; 
 //-------------------------------------------------------------
  reg [IRLength-1:0] NextIRreg; 
  reg [IRLength-1:0] ir_int; // = IR_CAPTURE_VAL[IRLength-1:0] ;
  reg [IDLength-1:0] IDreg;
        
//####################################################################
//#####                     Initialize                           #####
//####################################################################
   initial begin
      case (PART_NAME)
                "7A15T",        "7a15t"         : IDCODEval_sig <= 32'h0362E093;
                "7A25T",        "7a25t"         : IDCODEval_sig <= 32'h037C2093;
                "7A35T",        "7a35t"         : IDCODEval_sig <= 32'h0362D093;
                "7A50T",        "7a50t"         : IDCODEval_sig <= 32'h0362C093;
                "7A75T",        "7a75t"         : IDCODEval_sig <= 32'h03632093;
                "7A100T",       "7a100t"        : IDCODEval_sig <= 32'h03631093;
                "7A200T",       "7a200t"        : IDCODEval_sig <= 32'h03636093;
                "7K70T",        "7k70t"         : IDCODEval_sig <= 32'h03647093;
                "7K160T",       "7k160t"        : IDCODEval_sig <= 32'h0364C093;
                "7K325T",       "7k325t"        : IDCODEval_sig <= 32'h03651093;
                "7K355T",       "7k355t"        : IDCODEval_sig <= 32'h03747093;
                "7K410T",       "7k410t"        : IDCODEval_sig <= 32'h03656093;
                "7K420T",       "7k420t"        : IDCODEval_sig <= 32'h03752093;
                "7K480T",       "7k480t"        : IDCODEval_sig <= 32'h03751093;
                "7S15",         "7s15"          : IDCODEval_sig <= 32'h03620093;
                "7S100",        "7s100"         : IDCODEval_sig <= 32'h037C7093;
                "7V585T",       "7v585t"        : IDCODEval_sig <= 32'h03671093;
                "7V2000T",      "7v2000t"       : IDCODEval_sig <= 32'h036B3093;
                "7VH580T",      "7vh580t"       : IDCODEval_sig <= 32'h036D9093;
                "7VH870T",      "7vh870t"       : IDCODEval_sig <= 32'h036DB093;
                "7VX330T",      "7vx330t"       : IDCODEval_sig <= 32'h03667093;
                "7VX415T",      "7vx415t"       : IDCODEval_sig <= 32'h03682093;
                "7VX485T",      "7vx485t"       : IDCODEval_sig <= 32'h03687093;
                "7VX550T",      "7vx550t"       : IDCODEval_sig <= 32'h03692093;
                "7VX690T",      "7vx690t"       : IDCODEval_sig <= 32'h03691093;
                "7VX980T",      "7vx980t"       : IDCODEval_sig <= 32'h03696093;
                "7VX1140T",     "7vx1140t"      : IDCODEval_sig <= 32'h036D5093;
                "7Z010",        "7z010"         : IDCODEval_sig <= 32'h03722093;
                "7Z015",        "7z015"         : IDCODEval_sig <= 32'h0373B093;
                "7Z020",        "7z020"         : IDCODEval_sig <= 32'h03727093;
                "7Z030",        "7z030"         : IDCODEval_sig <= 32'h0372C093;
                "7Z035",        "7z035"         : IDCODEval_sig <= 32'h03732093;
                "7Z045",        "7z045"         : IDCODEval_sig <= 32'h03731093;
                "7Z100",        "7z100"         : IDCODEval_sig <= 32'h03736093;
                "7Z007S",       "7z007s"        : IDCODEval_sig <= 32'h03723093;
                "7Z012S",       "7z012s"        : IDCODEval_sig <= 32'h0373C093;
                "7Z014S",       "7z014s"        : IDCODEval_sig <= 32'h03728093;
                "KU025",        "ku025"         : IDCODEval_sig <= 32'h03824093;
                "KU035",        "ku035"         : IDCODEval_sig <= 32'h03823093;
                "KU040",        "ku040"         : IDCODEval_sig <= 32'h03822093;
                "KU060",        "ku060"         : IDCODEval_sig <= 32'h03919093;
                "KU085",        "ku085"         : IDCODEval_sig <= 32'h0390F093;
                "KU095",        "ku095"         : IDCODEval_sig <= 32'h03844093;
                "KU115",        "ku115"         : IDCODEval_sig <= 32'h0390D093;
                "VU065",        "vu065"         : IDCODEval_sig <= 32'h03939093;
                "VU080",        "vu080"         : IDCODEval_sig <= 32'h03843093;
                "VU095",        "vu095"         : IDCODEval_sig <= 32'h03842093;
                "VU125",        "vu125"         : IDCODEval_sig <= 32'h0392D093;
                "VU160",        "vu160"         : IDCODEval_sig <= 32'h03933093;
                "VU190",        "vu190"         : IDCODEval_sig <= 32'h03931093;
                "VU440",        "vu440"         : IDCODEval_sig <= 32'h0396D093;
                "XCKU3P",       "xcku3p"        : IDCODEval_sig <= 32'h04A46093;
                "XCKU9P",       "xcku9p"        : IDCODEval_sig <= 32'h0484A093;
                "XCKU11P",      "xcku11p"       : IDCODEval_sig <= 32'h04A4E093;
                "XCKU13EG",     "xcku13eg"      : IDCODEval_sig <= 32'h04A52093;
                "XCKU15P",      "xcku15p"       : IDCODEval_sig <= 32'h04A56093;
                "XCKU5P",       "xcku5p"        : IDCODEval_sig <= 32'h04A62093;
                "XCVU3P",       "xcvu3p"        : IDCODEval_sig <= 32'h04B39093;
                "XCZU9EG",      "xczu9eg"       : IDCODEval_sig <= 32'h04738093;
                "XCVU5P",       "xcvu5p"        : IDCODEval_sig <= 32'h04B2B093;
                "XCVU7P",       "xcvu7p"        : IDCODEval_sig <= 32'h04B29093;
                "XCZU3EG",      "xczu3eg"       : IDCODEval_sig <= 32'h04710093;
                "XCZU4EG",      "xczu4eg"       : IDCODEval_sig <= 32'h04A47093;
                "XCZU5EG",      "xczu5eg"       : IDCODEval_sig <= 32'h04A46093;
                "XCZU7EG",      "xczu7eg"       : IDCODEval_sig <= 32'h04A5A093;
                "XCZU2CG",      "xczu2cg"       : IDCODEval_sig <= 32'h04A43093;
                "XCZU3CG",      "xczu3cg"       : IDCODEval_sig <= 32'h04A42093;
                "XCZU4CG",      "xczu4cg"       : IDCODEval_sig <= 32'h04A47093;
                "XCZU5CG",      "xczu5cg"       : IDCODEval_sig <= 32'h04A46093;
                "XCZU6CG",      "xczu6cg"       : IDCODEval_sig <= 32'h0484B093;
                "XCZU7CG",      "xczu7cg"       : IDCODEval_sig <= 32'h04A5A093;
                "XCZU9CG",      "xczu9cg"       : IDCODEval_sig <= 32'h0484A093;
                "XCZU5EV",      "xczu5ev"       : IDCODEval_sig <= 32'h04720093;
                "XCZU11EG",     "xczu11eg"      : IDCODEval_sig <= 32'h04740093;
                "XCZU15EG",     "xczu15eg"      : IDCODEval_sig <= 32'h04750093;
                "XCZU19EG",     "xczu19eg"      : IDCODEval_sig <= 32'h04758093;
                "XCZU7EV",      "xczu7ev"       : IDCODEval_sig <= 32'h04730093;
                "XCZU2EG",      "xczu2eg"       : IDCODEval_sig <= 32'h04A43093;
                "XCZU4EV",      "xczu4ev"       : IDCODEval_sig <= 32'h04A47093;
                "XCZU6EG",      "xczu6eg"       : IDCODEval_sig <= 32'h04A4B093;
                "XCZU17EG",     "xczu17eg"      : IDCODEval_sig <= 32'h04A57093;
                "XCVU9P",       "xcvu9p"        : IDCODEval_sig <= 32'h04B31093;
                "XCVU11P",      "xcvu11p"       : IDCODEval_sig <= 32'h04B42093;
                "XCVU13P",      "xcvu13p"       : IDCODEval_sig <= 32'h04B51093;


         default : begin

                        $display("Attribute Syntax Error : The attribute PART_NAME on JTAG_SIME2 instance %m is set to %s. The legal values for this attributes are 7A15T, 7A35T, 7A50T, 7A75T, 7A100T, 7A200T, 7K70T, 7K160T, 7K325T, 7K355T, 7K410T, 7K420T, 7K480T, 7V585T, 7S15, 7S100, 7A25T, 7V2000T, 7VH580T, 7VH870T, 7VX330T, 7VX415T, 7VX485T, 7VX550T, 7VX690T, 7VX980T, 7VX1140T, 7Z010, 7Z015, 7Z020, 7Z030, 7Z035, 7Z045, 7Z100, 7Z007S, 7Z012S, 7Z014S, KU025, KU035, KU040, KU060, KU095, KU115, VU065, VU080, VU095, VU125, VU160, VU190, VU440, XCKU3P, XCKU9P, XCKU11P, XCKU13EG, XCKU15P, XCKU5P, XCVU3P, XCZU9EG, XCVU5P, XCVU7P, XCZU3EG, XCZU4EG, XCZU5EG, XCZU7EG, XCZU2CG, XCZU3CG, XCZU4CG, XCZU5CG, XCZU6CG, XCZU7CG, XCZU9CG, XCZU5EV, XCZU11EG, XCZU15EG, XCZU19EG, XCZU7EV, XCZU2EG, XCZU4EV, XCZU6EG, XCZU17EG, XCVU9P, XCVU11P or XCVU13P.",  PART_NAME);
         end
       endcase // case(PART_NAME)

       ir_int <= IR_CAPTURE_VAL[IRLength-1:0];

    end // initial begin
//####################################################################
//#####                      JtagTapSM                           #####
//####################################################################
  always@(posedge TCK or posedge TRST)
     begin
       if(TRST) begin
          CurrentState <= TestLogicReset;
       end
       else begin
            case(CurrentState)
 
               TestLogicReset:
                 begin
                   if(TMS == 0) begin
                      CurrentState <= RunTestIdle;
                      jtag_state_name <= "RunTestIdle";
                   end
                 end

               RunTestIdle:
                 begin
                   if(TMS == 1) begin
                      CurrentState <= SelectDRScan;
                      jtag_state_name <= "SelectDRScan";
                   end
                 end
               //-------------------------------
               // ------  DR path ---------------
               // -------------------------------
               SelectDRScan:
                 begin
                   if(TMS == 0) begin
                      CurrentState <= CaptureDR;
                      jtag_state_name <= "CaptureDR";
                   end
                   else if(TMS == 1) begin
                      CurrentState <= SelectIRScan;
                      jtag_state_name <= "SelectIRScan";
                   end
                 end
 
               CaptureDR:
                 begin
                   if(TMS == 0) begin
                      CurrentState <= ShiftDR;
                      jtag_state_name <= "ShiftDR";
                   end
                   else if(TMS == 1) begin
                      CurrentState <= Exit1DR;
                      jtag_state_name <= "Exit1DR";
                   end
                 end
              
               ShiftDR:
                 begin
                    if(IRcontent_sig == BYPASS_INSTR[IRLengthMax - 1 : (IRLengthMax - IRLength)]) 
                      BypassReg <= TDI;

                   if(TMS == 1) begin
                      CurrentState <= Exit1DR;
                      jtag_state_name <= "Exit1DR";
                   end
                 end
              
               Exit1DR:
                 begin
                   if(TMS == 0) begin
                      CurrentState <= PauseDR;
                      jtag_state_name <= "PauseDR";
                   end
                   else if(TMS == 1) begin
                      CurrentState <= UpdateDR;
                      jtag_state_name <= "UpdateDR";
                   end
                 end
              
               PauseDR:
                 begin
                   if(TMS == 1) begin
                      CurrentState <=  Exit2DR;
                      jtag_state_name <= "Exit2DR";
                   end
                 end
            
               Exit2DR:
                 begin
                   if(TMS == 0) begin
                      CurrentState <= ShiftDR;
                      jtag_state_name <= "ShiftDR";
                   end
                   else if(TMS == 1) begin
                      CurrentState <= UpdateDR;
                      jtag_state_name <= "UpdateDR";
                   end
                 end
              
               UpdateDR:
                 begin
                   if(TMS == 0) begin
                      CurrentState <= RunTestIdle;
                      jtag_state_name <= "RunTestIdle";
                   end
                   else if(TMS == 1) begin
                      CurrentState <= SelectDRScan;
                      jtag_state_name <= "SelectDRScan";
                   end
                 end
               //-------------------------------
               // ------  IR path ---------------
               // -------------------------------
               SelectIRScan:
                 begin
                   if(TMS == 0) begin
                      CurrentState <= CaptureIR;
                      jtag_state_name <= "CaptureIR";
                   end
                   else if(TMS == 1) begin
                      CurrentState <= TestLogicReset;
                      jtag_state_name <= "TestLogicReset";
                   end
                 end
 
               CaptureIR:
                 begin
                   if(TMS == 0) begin
                      CurrentState <= ShiftIR;
                      jtag_state_name <= "ShiftIR";
                   end
                   else if(TMS == 1) begin
                      CurrentState <= Exit1IR;
                      jtag_state_name <= "Exit1IR";
                   end
                  end
              
               ShiftIR:
                 begin
//                   ClkIR_sig <= 1;

                   if(TMS == 1) begin
                      CurrentState <= Exit1IR;
                      jtag_state_name <= "Exit1IR";
                   end
                 end
             
               Exit1IR:
                 begin
                   if(TMS == 0) begin
                      CurrentState <= PauseIR;
                      jtag_state_name <= "PauseIR";
                   end
                   else if(TMS == 1) begin
                      CurrentState <= UpdateIR;
                      jtag_state_name <= "UpdateIR";
                   end
                 end
              
               PauseIR:
                 begin
                   if(TMS == 1) begin
                      CurrentState <=  Exit2IR;
                      jtag_state_name <= "Exit2IR";
                   end
                 end
            
               Exit2IR:
                 begin
                   if(TMS == 0) begin
                      CurrentState <= ShiftIR;
                      jtag_state_name <= "ShiftIR";
                   end 
                   else if(TMS == 1) begin
                      CurrentState <= UpdateIR;
                      jtag_state_name <= "UpdateIR";
                   end
                 end
              
               UpdateIR:
                 begin
                  //-- FP
//                   ClkIR_sig <= 1;

                   if(TMS == 0) begin
                      CurrentState <= RunTestIdle;
                      jtag_state_name <= "RunTestIdle";
                   end
                   else if(TMS == 1) begin
                      CurrentState <= SelectDRScan;
                      jtag_state_name <= "SelectDRScan";
                   end
                 end
             endcase // case(CurrentState)
       end // else

     end // always

//--------------------------------------------------------
  always@(CurrentState, TCK, TRST)
  begin
      ClkIR_sig <= 1;

      if(TRST == 1 ) begin
            Tlrst_sig     <= #DELAY_SIG 1;
            CaptureDR_sig <= #DELAY_SIG 0;
            ShiftDR_sig   <= #DELAY_SIG 0;
            UpdateDR_sig  <= #DELAY_SIG 0;
            ShiftIR_sig   <= #DELAY_SIG 0;
            UpdateIR_sig  <= #DELAY_SIG 0;
      end
      else if(TRST == 0) begin
         
         case (CurrentState)
            TestLogicReset:  begin 
                  Tlrst_sig     <= #DELAY_SIG 1;
                  Rti_sig       <= #DELAY_SIG 0;
                  CaptureDR_sig <= #DELAY_SIG 0;
                  ShiftDR_sig   <= #DELAY_SIG 0;
                  UpdateDR_sig  <= #DELAY_SIG 0;
                  ShiftIR_sig   <= #DELAY_SIG 0;
                  UpdateIR_sig  <= #DELAY_SIG 0;
            end
            RunTestIdle:  begin 
                  Tlrst_sig     <= #DELAY_SIG 0;
                  Rti_sig       <= #DELAY_SIG 1;
                  CaptureDR_sig <= #DELAY_SIG 0;
                  ShiftDR_sig   <= #DELAY_SIG 0;
                  UpdateDR_sig  <= #DELAY_SIG 0;
                  ShiftIR_sig   <= #DELAY_SIG 0;
                  UpdateIR_sig  <= #DELAY_SIG 0;
            end
            CaptureDR:  begin 
                  Tlrst_sig     <= #DELAY_SIG 0;
                  Rti_sig       <= #DELAY_SIG 0;
                  CaptureDR_sig <= #DELAY_SIG 1;
                  ShiftDR_sig   <= #DELAY_SIG 0;
                  UpdateDR_sig  <= #DELAY_SIG 0;
                  ShiftIR_sig   <= #DELAY_SIG 0;
                  UpdateIR_sig  <= #DELAY_SIG 0;
            end
            ShiftDR:  begin 
                  Tlrst_sig     <= #DELAY_SIG 0;
                  Rti_sig       <= #DELAY_SIG 0;
                  CaptureDR_sig <= #DELAY_SIG 0;
                  ShiftDR_sig   <= #DELAY_SIG 1;
                  UpdateDR_sig  <= #DELAY_SIG 0;
                  ShiftIR_sig   <= #DELAY_SIG 0;
                  UpdateIR_sig  <= #DELAY_SIG 0;
            end
            UpdateDR:  begin 
                  Tlrst_sig     <= #DELAY_SIG 0;
                  Rti_sig       <= #DELAY_SIG 0;
                  CaptureDR_sig <= #DELAY_SIG 0;
                  ShiftDR_sig   <= #DELAY_SIG 0;
                  UpdateDR_sig  <= #DELAY_SIG 1;
                  ShiftIR_sig   <= #DELAY_SIG 0;
                  UpdateIR_sig  <= #DELAY_SIG 0;
            end
            CaptureIR:  begin 
                  Tlrst_sig     <= #DELAY_SIG 0;
                  Rti_sig       <= #DELAY_SIG 0;
                  CaptureDR_sig <= #DELAY_SIG 0;
                  ShiftDR_sig   <= #DELAY_SIG 0;
                  UpdateDR_sig  <= #DELAY_SIG 0;
                  ShiftIR_sig   <= #DELAY_SIG 0;
                  UpdateIR_sig  <= #DELAY_SIG 0;
                  ClkIR_sig     <= TCK;
            end
            ShiftIR:  begin 
                  Tlrst_sig     <= #DELAY_SIG 0;
                  Rti_sig       <= #DELAY_SIG 0;
                  CaptureDR_sig <= #DELAY_SIG 0;
                  ShiftDR_sig   <= #DELAY_SIG 0;
                  UpdateDR_sig  <= #DELAY_SIG 0;
                  ShiftIR_sig   <= #DELAY_SIG 1;
                  UpdateIR_sig  <= #DELAY_SIG 0;
                  ClkIR_sig     <= TCK;
            end
            UpdateIR: begin 
                         Tlrst_sig     <= #DELAY_SIG 0;
                         Rti_sig       <= #DELAY_SIG 0;
                         CaptureDR_sig <= #DELAY_SIG 0;
                         ShiftDR_sig   <= #DELAY_SIG 0;
                         UpdateDR_sig  <= #DELAY_SIG 0;
                         ShiftIR_sig   <= #DELAY_SIG 0;
                         UpdateIR_sig  <= #DELAY_SIG 1;
                     end
            default: begin 
                         Tlrst_sig     <= #DELAY_SIG 0;
                         Rti_sig       <= #DELAY_SIG 0;
                         CaptureDR_sig <= #DELAY_SIG 0;
                         ShiftDR_sig   <= #DELAY_SIG 0;
                         UpdateDR_sig  <= #DELAY_SIG 0;
                         ShiftIR_sig   <= #DELAY_SIG 0;
                         UpdateIR_sig  <= #DELAY_SIG 0;
                     end
         endcase

      end

    end // always(CurrentState)
//-----------------------------------------------------
  always@(TCK)
  begin
//       ClkIR_sig = ShiftIR_sig & TCK;
       ClkUpdateIR_sig = UpdateIR_sig & ~TCK;
  end // always
   
  always@(TCK)
  begin
       ClkID_sig = IDCODE_sig & TCK;
  end // always

//-------------- TCK  NEGATIVE EDGE activities ----------
  always@(negedge TCK)
  begin
     if(TCK == 0) begin
        glbl.JTAG_CAPTURE_GLBL <= CaptureDR_sig;
        glbl.JTAG_RESET_GLBL   <= Tlrst_sig;
        glbl.JTAG_RUNTEST_GLBL   <= Rti_sig;
        glbl.JTAG_SHIFT_GLBL   <= ShiftDR_sig;
        glbl.JTAG_UPDATE_GLBL  <= UpdateDR_sig;
        TlrstN_sig             <= Tlrst_sig;
     end
  end // always

//--####################################################################
//--#####                       JtagIR                             #####
//--####################################################################
   always@(posedge ClkIR_sig) begin
      NextIRreg = {TDI, ir_int[IRLength-1:1]};

      if ((TRST== 0) && (TlrstN_sig == 0)) begin
         if(ShiftIR_sig == 1) begin 
            ir_int = NextIRreg;
            IRegLastBit_sig = ir_int[0];
         end
         else begin
            ir_int = IR_CAPTURE_VAL; 
            IRegLastBit_sig = ir_int[0];
         end
      end
   end //always 
//--------------------------------------------------------
   always@(posedge ClkUpdateIR_sig or posedge TlrstN_sig or
           posedge TRST) begin
      if ((TRST== 1) || (TlrstN_sig == 1)) begin
         IRcontent_sig = IDCODE_INSTR[IRLengthMax - 1 : (IRLengthMax - IRLength)];
         IRegLastBit_sig = ir_int[0];
      end
      else if( (TRST == 0) && (TlrstN_sig == 0)) begin 
               IRcontent_sig = ir_int;
      end
   end //always 
//--####################################################################
//--#####                       JtagDecodeIR                       #####
//--####################################################################
   always@(IRcontent_sig) begin

      case(IRcontent_sig)

//          IR_CAPTURE_VAL : begin
//               ;
//               jtag_instruction_name = "IR_CAPTURE";
//          end

          BYPASS_INSTR[IRLengthMax - 1 : (IRLengthMax - IRLength)] : begin
             jtag_instruction_name = "BYPASS";
             // if BYPASS instruction, set BYPASS signal to 1
             BYPASS_sig <= 1;
             IDCODE_sig <= 0;
             USER1_sig  <= 0;
             USER2_sig  <= 0;
             USER3_sig  <= 0;
             USER4_sig  <= 0;
          end

          IDCODE_INSTR[IRLengthMax - 1 : (IRLengthMax - IRLength)] : begin
             jtag_instruction_name = "IDCODE";
             // if IDCODE instruction, set IDCODE signal to 1
             BYPASS_sig <= 0;
             IDCODE_sig <= 1;
             USER1_sig  <= 0;
             USER2_sig  <= 0;
             USER3_sig  <= 0;
             USER4_sig  <= 0;
          end

          USER1_INSTR[IRLengthMax - 1 : (IRLengthMax - IRLength)] : begin
             jtag_instruction_name = "USER1";
             // if USER1 instruction, set USER1 signal to 1 
             BYPASS_sig <= 0;
             IDCODE_sig <= 0;
             USER1_sig  <= 1;
             USER2_sig  <= 0;
             USER3_sig  <= 0;
             USER4_sig  <= 0;
          end

          USER2_INSTR[IRLengthMax - 1 : (IRLengthMax - IRLength)] : begin
             jtag_instruction_name = "USER2";
             // if USER2 instruction, set USER2 signal to 1 
             BYPASS_sig <= 0;
             IDCODE_sig <= 0;
             USER1_sig  <= 0;
             USER2_sig  <= 1;
             USER3_sig  <= 0;
             USER4_sig  <= 0;
          end

          USER3_INSTR[IRLengthMax - 1 : (IRLengthMax - IRLength)] : begin
             jtag_instruction_name = "USER3";
             // if USER3 instruction, set USER3 signal to 1 
             BYPASS_sig <= 0;
             USER1_sig  <= 0;
             USER2_sig  <= 0;
             IDCODE_sig <= 0;
             USER3_sig  <= 1;
             USER4_sig  <= 0;
           end

          USER4_INSTR[IRLengthMax - 1 : (IRLengthMax - IRLength)] : begin
             jtag_instruction_name = "USER4";
             // if USER4 instruction, set USER4 signal to 1 
             BYPASS_sig <= 0;
             IDCODE_sig <= 0;
             USER1_sig  <= 0;
             USER2_sig  <= 0;
             USER3_sig  <= 0;
             USER4_sig  <= 1;
          end
          default : begin
             jtag_instruction_name = "UNKNOWN";
             // if UNKNOWN instruction, set all signals to 0 
             BYPASS_sig <= 0;
             IDCODE_sig <= 0;
             USER1_sig  <= 0;
             USER2_sig  <= 0;
             USER3_sig  <= 0;
             USER4_sig  <= 0;
          end

      endcase
   end //always
//--####################################################################
//--#####                       JtagIDCODE                         #####
//--####################################################################
   always@(posedge ClkID_sig) begin
//     reg [(IDLength -1) : 0] IDreg;
     if(ShiftDR_sig == 1) begin
        IDreg = IDreg >> 1;
        IDreg[IDLength -1] = TDI;
     end
     else
        IDreg = IDCODEval_sig;

     IDregLastBit_sig = IDreg[0];
   end // always

//--####################################################################
//--#####                    JtagSetGlobalSignals                  #####
//--####################################################################
   always@(ClkUpdateIR_sig, Tlrst_sig, USER1_sig, USER2_sig, USER3_sig, USER4_sig) begin
      if(Tlrst_sig == 1) begin 
         glbl.JTAG_SEL1_GLBL <= 0;
         glbl.JTAG_SEL2_GLBL <= 0;
         glbl.JTAG_SEL3_GLBL <= 0;
         glbl.JTAG_SEL4_GLBL <= 0;
      end
      else if(Tlrst_sig == 0) begin
              if(USER1_sig == 1) begin
                 glbl.JTAG_SEL1_GLBL <= USER1_sig;
                 glbl.JTAG_SEL2_GLBL <= 0;
                 glbl.JTAG_SEL3_GLBL <= 0;
                 glbl.JTAG_SEL4_GLBL <= 0;
              end
              else if(USER2_sig == 1) begin
                 glbl.JTAG_SEL1_GLBL <= 0;
                 glbl.JTAG_SEL2_GLBL <= 1;
                 glbl.JTAG_SEL3_GLBL <= 0;
                 glbl.JTAG_SEL4_GLBL <= 0;
              end
              else if(USER3_sig == 1) begin
                 glbl.JTAG_SEL1_GLBL <= 0;
                 glbl.JTAG_SEL2_GLBL <= 0;
                 glbl.JTAG_SEL3_GLBL <= 1;
                 glbl.JTAG_SEL4_GLBL <= 0;
              end
              else if(USER4_sig == 1) begin
                 glbl.JTAG_SEL1_GLBL <= 0;
                 glbl.JTAG_SEL2_GLBL <= 0;
                 glbl.JTAG_SEL3_GLBL <= 0;
                 glbl.JTAG_SEL4_GLBL <= 1;
              end
              else if(ClkUpdateIR_sig == 1) begin
                 glbl.JTAG_SEL1_GLBL <= 0;
                 glbl.JTAG_SEL2_GLBL <= 0;
                 glbl.JTAG_SEL3_GLBL <= 0;
                 glbl.JTAG_SEL4_GLBL <= 0;
              end

      end
       
   end //always

//--####################################################################
//--#####                         OUTPUT                           #####
//--####################################################################
  assign glbl.JTAG_TDI_GLBL = TDI;
  assign glbl.JTAG_TCK_GLBL = TCK;
  assign glbl.JTAG_TMS_GLBL = TMS;

  always@(CurrentState, IRcontent_sig, BypassReg,
          IRegLastBit_sig, IDregLastBit_sig,  glbl.JTAG_USER_TDO1_GLBL,
          glbl.JTAG_USER_TDO2_GLBL, glbl.JTAG_USER_TDO3_GLBL, 
          glbl.JTAG_USER_TDO4_GLBL) 
  begin
      case (CurrentState)
         ShiftIR:  begin
                      TDO_latch <= IRegLastBit_sig;
                   end 
         ShiftDR:  begin
                      if(IRcontent_sig == IDCODE_INSTR[IRLengthMax - 1 : (IRLengthMax - IRLength)]) 
                          TDO_latch <= IDregLastBit_sig;
                      else if(IRcontent_sig == BYPASS_INSTR[IRLengthMax - 1 : (IRLengthMax - IRLength)]) 
                          TDO_latch <= BypassReg; 
                      else if(IRcontent_sig == USER1_INSTR[IRLengthMax - 1 : (IRLengthMax - IRLength)]) 
                          TDO_latch <= glbl.JTAG_USER_TDO1_GLBL; 
                      else if(IRcontent_sig == USER2_INSTR[IRLengthMax - 1 : (IRLengthMax - IRLength)]) 
                          TDO_latch <= glbl.JTAG_USER_TDO2_GLBL; 
                      else if(IRcontent_sig == USER3_INSTR[IRLengthMax - 1 : (IRLengthMax - IRLength)]) 
                          TDO_latch <= glbl.JTAG_USER_TDO3_GLBL; 
                      else if(IRcontent_sig == USER4_INSTR[IRLengthMax - 1 : (IRLengthMax - IRLength)]) 
                          TDO_latch <= glbl.JTAG_USER_TDO4_GLBL; 
                      else
                          TDO_latch <= 1'bz;
                      end 
         default : begin
                          TDO_latch <= 1'bz;
                   end
      endcase // case(PART_NAME)
  end // always

  always@(negedge TCK)
  begin
// 213980 NCsim compile error fix
     TDO <= TDO_latch;
  end // always
   
//--####################################################################
//--#####                         Timing                           #####
//--####################################################################

`ifdef XIL_TIMING
    
  specify
// 213980 NCsim compile error fix
//     (TCK => TDO) = (6000:6000:6000, 6000:6000:6000);

     $setuphold (posedge TCK, posedge TDI , 1000:1000:1000, 2000:2000:2000, notifier);
     $setuphold (posedge TCK, negedge TDI , 1000:1000:1000, 2000:2000:2000, notifier);

     $setuphold (posedge TCK, posedge TMS , 1000:1000:1000, 2000:2000:2000, notifier);
     $setuphold (posedge TCK, negedge TMS , 1000:1000:1000, 2000:2000:2000, notifier);

  endspecify

`endif //  `ifdef XIL_TIMING
    
endmodule // JTAG_SIME2

`endcelldefine

