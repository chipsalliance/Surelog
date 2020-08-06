///////////////////////////////////////////////////////
//     Copyright (c) 2011 Xilinx Inc.
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
///////////////////////////////////////////////////////
//
//   ____   ___
//  /   /\/   / 
// /___/  \  /     Vendor      : Xilinx 
// \  \    \/      Version     :  13.1
//  \  \           Description : 
//  /  /                      
// /__/   /\       Filename    : GTPE2_COMMON.uniprim.v
// \  \  /  \ 
//  \__\/\__ \                    
//                                 
//  Revision:		1.0
//  11/8/12  - 686589 - YML default changes
//  01/18/13 - 695630 - added drp monitor
//  08/29/14 - 821138 - add negedge specify section for IS_INVERTED*CLK*
///////////////////////////////////////////////////////

`timescale 1 ps / 1 ps 
`celldefine
module GTPE2_COMMON (
  DMONITOROUT,
  DRPDO,
  DRPRDY,
  PLL0FBCLKLOST,
  PLL0LOCK,
  PLL0OUTCLK,
  PLL0OUTREFCLK,
  PLL0REFCLKLOST,
  PLL1FBCLKLOST,
  PLL1LOCK,
  PLL1OUTCLK,
  PLL1OUTREFCLK,
  PLL1REFCLKLOST,
  PMARSVDOUT,
  REFCLKOUTMONITOR0,
  REFCLKOUTMONITOR1,

  BGBYPASSB,
  BGMONITORENB,
  BGPDB,
  BGRCALOVRD,
  BGRCALOVRDENB,
  DRPADDR,
  DRPCLK,
  DRPDI,
  DRPEN,
  DRPWE,
  GTEASTREFCLK0,
  GTEASTREFCLK1,
  GTGREFCLK0,
  GTGREFCLK1,
  GTREFCLK0,
  GTREFCLK1,
  GTWESTREFCLK0,
  GTWESTREFCLK1,
  PLL0LOCKDETCLK,
  PLL0LOCKEN,
  PLL0PD,
  PLL0REFCLKSEL,
  PLL0RESET,
  PLL1LOCKDETCLK,
  PLL1LOCKEN,
  PLL1PD,
  PLL1REFCLKSEL,
  PLL1RESET,
  PLLRSVD1,
  PLLRSVD2,
  PMARSVD,
  RCALENB
);

  `ifdef XIL_TIMING //Simprim 
  parameter LOC = "UNPLACED";
  `endif
  parameter [63:0] BIAS_CFG = 64'h0000000000000000;
  parameter [31:0] COMMON_CFG = 32'h00000000;
  parameter [0:0] IS_DRPCLK_INVERTED = 1'b0;
  parameter [0:0] IS_GTGREFCLK0_INVERTED = 1'b0;
  parameter [0:0] IS_GTGREFCLK1_INVERTED = 1'b0;
  parameter [0:0] IS_PLL0LOCKDETCLK_INVERTED = 1'b0;
  parameter [0:0] IS_PLL1LOCKDETCLK_INVERTED = 1'b0;
  parameter [26:0] PLL0_CFG = 27'h01F03DC;
  parameter [0:0] PLL0_DMON_CFG = 1'b0;
  parameter integer PLL0_FBDIV = 4;
  parameter integer PLL0_FBDIV_45 = 5;
  parameter [23:0] PLL0_INIT_CFG = 24'h00001E;
  parameter [8:0] PLL0_LOCK_CFG = 9'h1E8;
  parameter integer PLL0_REFCLK_DIV = 1;
  parameter [26:0] PLL1_CFG = 27'h01F03DC;
  parameter [0:0] PLL1_DMON_CFG = 1'b0;
  parameter integer PLL1_FBDIV = 4;
  parameter integer PLL1_FBDIV_45 = 5;
  parameter [23:0] PLL1_INIT_CFG = 24'h00001E;
  parameter [8:0] PLL1_LOCK_CFG = 9'h1E8;
  parameter integer PLL1_REFCLK_DIV = 1;
  parameter [7:0] PLL_CLKOUT_CFG = 8'b00000000;
  parameter [15:0] RSVD_ATTR0 = 16'h0000;
  parameter [15:0] RSVD_ATTR1 = 16'h0000;
  parameter [2:0] SIM_PLL0REFCLK_SEL = 3'b001;
  parameter [2:0] SIM_PLL1REFCLK_SEL = 3'b001;
  parameter SIM_RESET_SPEEDUP = "TRUE";
  parameter SIM_VERSION = "1.0";

  localparam in_delay = 0;
  localparam out_delay = 0;
  localparam INCLK_DELAY = 0;
  localparam OUTCLK_DELAY = 0;

  output DRPRDY;
  output PLL0FBCLKLOST;
  output PLL0LOCK;
  output PLL0OUTCLK;
  output PLL0OUTREFCLK;
  output PLL0REFCLKLOST;
  output PLL1FBCLKLOST;
  output PLL1LOCK;
  output PLL1OUTCLK;
  output PLL1OUTREFCLK;
  output PLL1REFCLKLOST;
  output REFCLKOUTMONITOR0;
  output REFCLKOUTMONITOR1;
  output [15:0] DRPDO;
  output [15:0] PMARSVDOUT;
  output [7:0] DMONITOROUT;

  input BGBYPASSB;
  input BGMONITORENB;
  input BGPDB;
  input BGRCALOVRDENB;
  input DRPCLK;
  input DRPEN;
  input DRPWE;
  input GTEASTREFCLK0;
  input GTEASTREFCLK1;
  input GTGREFCLK0;
  input GTGREFCLK1;
  input GTREFCLK0;
  input GTREFCLK1;
  input GTWESTREFCLK0;
  input GTWESTREFCLK1;
  input PLL0LOCKDETCLK;
  input PLL0LOCKEN;
  input PLL0PD;
  input PLL0RESET;
  input PLL1LOCKDETCLK;
  input PLL1LOCKEN;
  input PLL1PD;
  input PLL1RESET;
  input RCALENB;
  input [15:0] DRPDI;
  input [15:0] PLLRSVD1;
  input [2:0] PLL0REFCLKSEL;
  input [2:0] PLL1REFCLKSEL;
  input [4:0] BGRCALOVRD;
  input [4:0] PLLRSVD2;
  input [7:0] DRPADDR;
  input [7:0] PMARSVD;

  reg SIM_RESET_SPEEDUP_BINARY;
  reg SIM_VERSION_BINARY;
  reg [0:0] PLL0_DMON_CFG_BINARY;
  reg [0:0] PLL0_FBDIV_45_BINARY;
  reg [0:0] PLL1_DMON_CFG_BINARY;
  reg [0:0] PLL1_FBDIV_45_BINARY;
  reg [2:0] SIM_PLL0REFCLK_SEL_BINARY;
  reg [2:0] SIM_PLL1REFCLK_SEL_BINARY;
  reg [4:0] PLL0_REFCLK_DIV_BINARY;
  reg [4:0] PLL1_REFCLK_DIV_BINARY;
  reg [5:0] PLL0_FBDIV_BINARY;
  reg [5:0] PLL1_FBDIV_BINARY;
  reg [7:0] PLL_CLKOUT_CFG_BINARY;

  tri0 GSR = glbl.GSR;
  reg notifier;

  initial begin
    case (PLL0_FBDIV)
      4 : PLL0_FBDIV_BINARY = 6'b000010;
      1 : PLL0_FBDIV_BINARY = 6'b010000;
      2 : PLL0_FBDIV_BINARY = 6'b000000;
      3 : PLL0_FBDIV_BINARY = 6'b000001;
      5 : PLL0_FBDIV_BINARY = 6'b000011;
      6 : PLL0_FBDIV_BINARY = 6'b000101;
      8 : PLL0_FBDIV_BINARY = 6'b000110;
      10 : PLL0_FBDIV_BINARY = 6'b000111;
      12 : PLL0_FBDIV_BINARY = 6'b001101;
      16 : PLL0_FBDIV_BINARY = 6'b001110;
      20 : PLL0_FBDIV_BINARY = 6'b001111;
      default : begin
        $display("Attribute Syntax Error : The Attribute PLL0_FBDIV on X_GTPE2_COMMON instance %m is set to %d.  Legal values for this attribute are 1 to 20.", PLL0_FBDIV, 4);
        #1 $finish;
      end
    endcase

    case (PLL0_FBDIV_45)
      5 : PLL0_FBDIV_45_BINARY = 1'b1;
      4 : PLL0_FBDIV_45_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute PLL0_FBDIV_45 on X_GTPE2_COMMON instance %m is set to %d.  Legal values for this attribute are 4 to 5.", PLL0_FBDIV_45, 5);
        #1 $finish;
      end
    endcase

    case (PLL0_REFCLK_DIV)
      1 : PLL0_REFCLK_DIV_BINARY = 5'b10000;
      2 : PLL0_REFCLK_DIV_BINARY = 5'b00000;
      3 : PLL0_REFCLK_DIV_BINARY = 5'b00001;
      4 : PLL0_REFCLK_DIV_BINARY = 5'b00010;
      5 : PLL0_REFCLK_DIV_BINARY = 5'b00011;
      6 : PLL0_REFCLK_DIV_BINARY = 5'b00101;
      8 : PLL0_REFCLK_DIV_BINARY = 5'b00110;
      10 : PLL0_REFCLK_DIV_BINARY = 5'b00111;
      12 : PLL0_REFCLK_DIV_BINARY = 5'b01101;
      16 : PLL0_REFCLK_DIV_BINARY = 5'b01110;
      20 : PLL0_REFCLK_DIV_BINARY = 5'b01111;
      default : begin
        $display("Attribute Syntax Error : The Attribute PLL0_REFCLK_DIV on X_GTPE2_COMMON instance %m is set to %d.  Legal values for this attribute are 1 to 20.", PLL0_REFCLK_DIV, 1);
        #1 $finish;
      end
    endcase

    case (PLL1_FBDIV)
      4 : PLL1_FBDIV_BINARY = 6'b000010;
      1 : PLL1_FBDIV_BINARY = 6'b010000;
      2 : PLL1_FBDIV_BINARY = 6'b000000;
      3 : PLL1_FBDIV_BINARY = 6'b000001;
      5 : PLL1_FBDIV_BINARY = 6'b000011;
      6 : PLL1_FBDIV_BINARY = 6'b000101;
      8 : PLL1_FBDIV_BINARY = 6'b000110;
      10 : PLL1_FBDIV_BINARY = 6'b000111;
      12 : PLL1_FBDIV_BINARY = 6'b001101;
      16 : PLL1_FBDIV_BINARY = 6'b001110;
      20 : PLL1_FBDIV_BINARY = 6'b001111;
      default : begin
        $display("Attribute Syntax Error : The Attribute PLL1_FBDIV on X_GTPE2_COMMON instance %m is set to %d.  Legal values for this attribute are 1 to 20.", PLL1_FBDIV, 4);
        #1 $finish;
      end
    endcase

    case (PLL1_FBDIV_45)
      5 : PLL1_FBDIV_45_BINARY = 1'b1;
      4 : PLL1_FBDIV_45_BINARY = 1'b0;
      default : begin
        $display("Attribute Syntax Error : The Attribute PLL1_FBDIV_45 on X_GTPE2_COMMON instance %m is set to %d.  Legal values for this attribute are 4 to 5.", PLL1_FBDIV_45, 5);
        #1 $finish;
      end
    endcase

    case (PLL1_REFCLK_DIV)
      1 : PLL1_REFCLK_DIV_BINARY = 5'b10000;
      2 : PLL1_REFCLK_DIV_BINARY = 5'b00000;
      3 : PLL1_REFCLK_DIV_BINARY = 5'b00001;
      4 : PLL1_REFCLK_DIV_BINARY = 5'b00010;
      5 : PLL1_REFCLK_DIV_BINARY = 5'b00011;
      6 : PLL1_REFCLK_DIV_BINARY = 5'b00101;
      8 : PLL1_REFCLK_DIV_BINARY = 5'b00110;
      10 : PLL1_REFCLK_DIV_BINARY = 5'b00111;
      12 : PLL1_REFCLK_DIV_BINARY = 5'b01101;
      16 : PLL1_REFCLK_DIV_BINARY = 5'b01110;
      20 : PLL1_REFCLK_DIV_BINARY = 5'b01111;
      default : begin
        $display("Attribute Syntax Error : The Attribute PLL1_REFCLK_DIV on X_GTPE2_COMMON instance %m is set to %d.  Legal values for this attribute are 1 to 20.", PLL1_REFCLK_DIV, 1);
        #1 $finish;
      end
    endcase

    case (SIM_RESET_SPEEDUP)
      "TRUE" : SIM_RESET_SPEEDUP_BINARY = 0;
      "FALSE" : SIM_RESET_SPEEDUP_BINARY = 0;
      default : begin
        $display("Attribute Syntax Error : The Attribute SIM_RESET_SPEEDUP on X_GTPE2_COMMON instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", SIM_RESET_SPEEDUP);
        #1 $finish;
      end
    endcase

    case (SIM_VERSION)
      "1.0" : SIM_VERSION_BINARY = 0;
      "1.1" : SIM_VERSION_BINARY = 0;
      "2.0" : SIM_VERSION_BINARY = 0;
      default : begin
        $display("Attribute Syntax Error : The Attribute SIM_VERSION on X_GTPE2_COMMON instance %m is set to %s.  Legal values for this attribute are 1.0, 1.1, or 2.0.", SIM_VERSION);
        #1 $finish;
      end
    endcase

    if ((PLL0_DMON_CFG >= 1'b0) && (PLL0_DMON_CFG <= 1'b1))
      PLL0_DMON_CFG_BINARY = PLL0_DMON_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute PLL0_DMON_CFG on X_GTPE2_COMMON instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", PLL0_DMON_CFG);
      #1 $finish;
    end

    if ((PLL1_DMON_CFG >= 1'b0) && (PLL1_DMON_CFG <= 1'b1))
      PLL1_DMON_CFG_BINARY = PLL1_DMON_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute PLL1_DMON_CFG on X_GTPE2_COMMON instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", PLL1_DMON_CFG);
      #1 $finish;
    end

    if ((PLL_CLKOUT_CFG >= 8'b00000000) && (PLL_CLKOUT_CFG <= 8'b11111111))
      PLL_CLKOUT_CFG_BINARY = PLL_CLKOUT_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute PLL_CLKOUT_CFG on X_GTPE2_COMMON instance %m is set to %b.  Legal values for this attribute are 8'b00000000 to 8'b11111111.", PLL_CLKOUT_CFG);
      #1 $finish;
    end

    if ((SIM_PLL0REFCLK_SEL >= 3'b0) && (SIM_PLL0REFCLK_SEL <= 3'b111))
      SIM_PLL0REFCLK_SEL_BINARY = SIM_PLL0REFCLK_SEL;
    else begin
      $display("Attribute Syntax Error : The Attribute SIM_PLL0REFCLK_SEL on X_GTPE2_COMMON instance %m is set to %b.  Legal values for this attribute are 3'b0 to 3'b111.", SIM_PLL0REFCLK_SEL);
      #1 $finish;
    end

    if ((SIM_PLL1REFCLK_SEL >= 3'b0) && (SIM_PLL1REFCLK_SEL <= 3'b111))
      SIM_PLL1REFCLK_SEL_BINARY = SIM_PLL1REFCLK_SEL;
    else begin
      $display("Attribute Syntax Error : The Attribute SIM_PLL1REFCLK_SEL on X_GTPE2_COMMON instance %m is set to %b.  Legal values for this attribute are 3'b0 to 3'b111.", SIM_PLL1REFCLK_SEL);
      #1 $finish;
    end

  end

  wire [15:0] delay_DRPDO;
  wire [15:0] delay_PMARSVDOUT;
  wire [7:0] delay_DMONITOROUT;
  wire delay_DRPRDY;
  wire delay_PLL0FBCLKLOST;
  wire delay_PLL0LOCK;
  wire delay_PLL0OUTCLK;
  wire delay_PLL0OUTREFCLK;
  wire delay_PLL0REFCLKLOST;
  wire delay_PLL1FBCLKLOST;
  wire delay_PLL1LOCK;
  wire delay_PLL1OUTCLK;
  wire delay_PLL1OUTREFCLK;
  wire delay_PLL1REFCLKLOST;
  wire delay_REFCLKOUTMONITOR0;
  wire delay_REFCLKOUTMONITOR1;

  wire [15:0] delay_DRPDI;
  wire [15:0] delay_PLLRSVD1;
  wire [2:0] delay_PLL0REFCLKSEL;
  wire [2:0] delay_PLL1REFCLKSEL;
  wire [4:0] delay_BGRCALOVRD;
  wire [4:0] delay_PLLRSVD2;
  wire [7:0] delay_DRPADDR;
  wire [7:0] delay_PMARSVD;
  wire delay_BGBYPASSB;
  wire delay_BGMONITORENB;
  wire delay_BGPDB;
  wire delay_BGRCALOVRDENB;
  wire delay_DRPCLK;
  wire delay_DRPEN;
  wire delay_DRPWE;
  wire delay_GTEASTREFCLK0;
  wire delay_GTEASTREFCLK1;
  wire delay_GTGREFCLK0;
  wire delay_GTGREFCLK1;
  wire delay_GTREFCLK0;
  wire delay_GTREFCLK1;
  wire delay_GTWESTREFCLK0;
  wire delay_GTWESTREFCLK1;
  wire delay_PLL0LOCKDETCLK;
  wire delay_PLL0LOCKEN;
  wire delay_PLL0PD;
  wire delay_PLL0RESET;
  wire delay_PLL1LOCKDETCLK;
  wire delay_PLL1LOCKEN;
  wire delay_PLL1PD;
  wire delay_PLL1RESET;
  wire delay_RCALENB;


   //drp monitor
   reg drpen_r1 = 1'b0;
   reg drpen_r2 = 1'b0;
   reg drpwe_r1 = 1'b0;
   reg drpwe_r2 = 1'b0;
   
   reg [1:0] sfsm = 2'b01;
    
   localparam FSM_IDLE = 2'b01;  
   localparam FSM_WAIT = 2'b10;
  

   always @(posedge delay_DRPCLK)
     begin
	// pipeline the DRPEN and DRPWE
        drpen_r1 <= delay_DRPEN;
        drpwe_r1 <= delay_DRPWE;
	drpen_r2 <= drpen_r1;
        drpwe_r2 <= drpwe_r1;

	
	// Check -  if DRPEN or DRPWE is more than 1 DCLK
	if ((drpen_r1 == 1'b1) && (drpen_r2 == 1'b1)) 
	  begin
	     $display("DRC Error : DRPEN is high for more than 1 DRPCLK on %m instance");
	     $finish; 
          end
	
	if ((drpwe_r1 == 1'b1) && (drpwe_r2 == 1'b1))
	  begin
             $display("DRC Error : DRPWE is high for more than 1 DRPCLK on %m instance");
             $finish;
          end


	//After the 1st DRPEN pulse, check the DRPEN and DRPRDY.
	case (sfsm)
          FSM_IDLE:   
            begin
               if(delay_DRPEN == 1'b1)
		 sfsm <= FSM_WAIT;  
            end
          
          FSM_WAIT:
            begin
               // After the 1st DRPEN, 4 cases can happen
               // DRPEN DRPRDY NEXT STATE
               // 0     0      FSM_WAIT - wait for DRPRDY
               // 0     1      FSM_IDLE - normal operation
               // 1     0      FSM_WAIT - display error and wait for DRPRDY
               // 1     1      FSM_WAIT - normal operation. Per UG470, DRPEN and DRPRDY can be at the same cycle.
               
               //Add the check for another DPREN pulse
               if(delay_DRPEN === 1'b1 && delay_DRPRDY === 1'b0) 
		 begin
		    $display("DRC Error : DRPEN is enabled before DRPRDY returns on %m instance");  
		    $finish;
		 end

               //Add the check for another DRPWE pulse
               if ((delay_DRPWE === 1'b1) && (delay_DRPEN === 1'b0))
		 begin
		    $display("DRC Error : DRPWE is enabled before DRPRDY returns on %m instance");
		    $finish;
		 end
                    
               if ((delay_DRPRDY === 1'b1) && (delay_DRPEN === 1'b0))
		 begin
		    sfsm <= FSM_IDLE;
		 end  
               
               if ((delay_DRPRDY === 1'b1)&& (delay_DRPEN === 1'b1))
		 begin
		    sfsm <= FSM_WAIT;
		 end  
            end
        
          default:                  
            begin
               $display("DRC Error : Default state in DRP FSM.");
               $finish;
            end
	endcase

     end // always @ (posedge delay_DRPCLK)
   //end drp monitor      

  reg [0:0] IS_DRPCLK_INVERTED_REG = IS_DRPCLK_INVERTED;
  reg [0:0] IS_GTGREFCLK0_INVERTED_REG = IS_GTGREFCLK0_INVERTED;
  reg [0:0] IS_GTGREFCLK1_INVERTED_REG = IS_GTGREFCLK1_INVERTED;
  reg [0:0] IS_PLL0LOCKDETCLK_INVERTED_REG = IS_PLL0LOCKDETCLK_INVERTED;
  reg [0:0] IS_PLL1LOCKDETCLK_INVERTED_REG = IS_PLL1LOCKDETCLK_INVERTED;

  assign #(OUTCLK_DELAY) PLL0OUTCLK = delay_PLL0OUTCLK;
  assign #(OUTCLK_DELAY) PLL1OUTCLK = delay_PLL1OUTCLK;
  assign #(OUTCLK_DELAY) REFCLKOUTMONITOR0 = delay_REFCLKOUTMONITOR0;
  assign #(OUTCLK_DELAY) REFCLKOUTMONITOR1 = delay_REFCLKOUTMONITOR1;

  assign #(out_delay) DMONITOROUT = delay_DMONITOROUT;
  assign #(out_delay) DRPDO = delay_DRPDO;
  assign #(out_delay) DRPRDY = delay_DRPRDY;
  assign #(out_delay) PLL0FBCLKLOST = delay_PLL0FBCLKLOST;
  assign #(out_delay) PLL0LOCK = delay_PLL0LOCK;
  assign #(out_delay) PLL0OUTREFCLK = delay_PLL0OUTREFCLK;
  assign #(out_delay) PLL0REFCLKLOST = delay_PLL0REFCLKLOST;
  assign #(out_delay) PLL1FBCLKLOST = delay_PLL1FBCLKLOST;
  assign #(out_delay) PLL1LOCK = delay_PLL1LOCK;
  assign #(out_delay) PLL1OUTREFCLK = delay_PLL1OUTREFCLK;
  assign #(out_delay) PLL1REFCLKLOST = delay_PLL1REFCLKLOST;
  assign #(out_delay) PMARSVDOUT = delay_PMARSVDOUT;
  
`ifndef XIL_TIMING // unisim
  assign #(INCLK_DELAY) delay_DRPCLK = DRPCLK ^ IS_DRPCLK_INVERTED_REG;
  assign #(INCLK_DELAY) delay_GTEASTREFCLK0 = GTEASTREFCLK0 ^ IS_GTGREFCLK0_INVERTED_REG;
  assign #(INCLK_DELAY) delay_GTEASTREFCLK1 = GTEASTREFCLK1  ^ IS_GTGREFCLK1_INVERTED_REG;
  assign #(INCLK_DELAY) delay_GTGREFCLK0 = GTGREFCLK0;
  assign #(INCLK_DELAY) delay_GTGREFCLK1 = GTGREFCLK1;
  assign #(INCLK_DELAY) delay_GTREFCLK0 = GTREFCLK0;
  assign #(INCLK_DELAY) delay_GTREFCLK1 = GTREFCLK1;
  assign #(INCLK_DELAY) delay_GTWESTREFCLK0 = GTWESTREFCLK0;
  assign #(INCLK_DELAY) delay_GTWESTREFCLK1 = GTWESTREFCLK1;
  assign #(INCLK_DELAY) delay_PLL0LOCKDETCLK = PLL0LOCKDETCLK ^ IS_PLL0LOCKDETCLK_INVERTED_REG;
  assign #(INCLK_DELAY) delay_PLL1LOCKDETCLK = PLL1LOCKDETCLK^ IS_PLL1LOCKDETCLK_INVERTED_REG;

  assign #(in_delay) delay_BGBYPASSB = BGBYPASSB;
  assign #(in_delay) delay_BGMONITORENB = BGMONITORENB;
  assign #(in_delay) delay_BGPDB = BGPDB;
  assign #(in_delay) delay_BGRCALOVRD = BGRCALOVRD;
  assign #(in_delay) delay_BGRCALOVRDENB = BGRCALOVRDENB;
  assign #(in_delay) delay_DRPADDR = DRPADDR;
  assign #(in_delay) delay_DRPDI = DRPDI;
  assign #(in_delay) delay_DRPEN = DRPEN;
  assign #(in_delay) delay_DRPWE = DRPWE;
  assign #(in_delay) delay_PLL0LOCKEN = PLL0LOCKEN;
  assign #(in_delay) delay_PLL0PD = PLL0PD;
  assign #(in_delay) delay_PLL0REFCLKSEL = PLL0REFCLKSEL;
  assign #(in_delay) delay_PLL0RESET = PLL0RESET;
  assign #(in_delay) delay_PLL1LOCKEN = PLL1LOCKEN;
  assign #(in_delay) delay_PLL1PD = PLL1PD;
  assign #(in_delay) delay_PLL1REFCLKSEL = PLL1REFCLKSEL;
  assign #(in_delay) delay_PLL1RESET = PLL1RESET;
  assign #(in_delay) delay_PLLRSVD1 = PLLRSVD1;
  assign #(in_delay) delay_PLLRSVD2 = PLLRSVD2;
  assign #(in_delay) delay_PMARSVD = PMARSVD;
  assign #(in_delay) delay_RCALENB = RCALENB;
`endif //  `ifndef XIL_TIMING

`ifdef XIL_TIMING //Simprim
  assign delay_BGBYPASSB = BGBYPASSB;
  assign delay_BGMONITORENB = BGMONITORENB;
  assign delay_BGPDB = BGPDB;
  assign delay_BGRCALOVRD = BGRCALOVRD;
  assign delay_BGRCALOVRDENB = BGRCALOVRDENB;
  assign delay_GTEASTREFCLK0 = GTEASTREFCLK0;
  assign delay_GTEASTREFCLK1 = GTEASTREFCLK1;
  assign delay_GTGREFCLK0 = GTGREFCLK0;
  assign delay_GTGREFCLK1 = GTGREFCLK1;
  assign delay_GTREFCLK0 = GTREFCLK0;
  assign delay_GTREFCLK1 = GTREFCLK1;
  assign delay_GTWESTREFCLK0 = GTWESTREFCLK0;
  assign delay_GTWESTREFCLK1 = GTWESTREFCLK1;
  assign delay_PLL0LOCKDETCLK = PLL0LOCKDETCLK;
  assign delay_PLL0LOCKEN = PLL0LOCKEN;
  assign delay_PLL0PD = PLL0PD;
  assign delay_PLL0REFCLKSEL = PLL0REFCLKSEL;
  assign delay_PLL0RESET = PLL0RESET;
  assign delay_PLL1LOCKDETCLK = PLL1LOCKDETCLK;
  assign delay_PLL1LOCKEN = PLL1LOCKEN;
  assign delay_PLL1PD = PLL1PD;
  assign delay_PLL1REFCLKSEL = PLL1REFCLKSEL;
  assign delay_PLL1RESET = PLL1RESET;
  assign delay_PLLRSVD1 = PLLRSVD1;
  assign delay_PLLRSVD2 = PLLRSVD2;
  assign delay_PMARSVD = PMARSVD;
  assign delay_RCALENB = RCALENB;

  wire drpclk_en_p;
  wire drpclk_en_n;

  assign drpclk_en_p = ~IS_DRPCLK_INVERTED;
  assign drpclk_en_n = IS_DRPCLK_INVERTED;
`endif

  B_GTPE2_COMMON #(
    .BIAS_CFG (BIAS_CFG),
    .COMMON_CFG (COMMON_CFG),
    .PLL0_CFG (PLL0_CFG),
    .PLL0_DMON_CFG (PLL0_DMON_CFG),
    .PLL0_FBDIV (PLL0_FBDIV),
    .PLL0_FBDIV_45 (PLL0_FBDIV_45),
    .PLL0_INIT_CFG (PLL0_INIT_CFG),
    .PLL0_LOCK_CFG (PLL0_LOCK_CFG),
    .PLL0_REFCLK_DIV (PLL0_REFCLK_DIV),
    .PLL1_CFG (PLL1_CFG),
    .PLL1_DMON_CFG (PLL1_DMON_CFG),
    .PLL1_FBDIV (PLL1_FBDIV),
    .PLL1_FBDIV_45 (PLL1_FBDIV_45),
    .PLL1_INIT_CFG (PLL1_INIT_CFG),
    .PLL1_LOCK_CFG (PLL1_LOCK_CFG),
    .PLL1_REFCLK_DIV (PLL1_REFCLK_DIV),
    .PLL_CLKOUT_CFG (PLL_CLKOUT_CFG),
    .RSVD_ATTR0 (RSVD_ATTR0),
    .RSVD_ATTR1 (RSVD_ATTR1),
    .SIM_PLL0REFCLK_SEL (SIM_PLL0REFCLK_SEL),
    .SIM_PLL1REFCLK_SEL (SIM_PLL1REFCLK_SEL),
    .SIM_RESET_SPEEDUP (SIM_RESET_SPEEDUP),
    .SIM_VERSION (SIM_VERSION))

    B_GTPE2_COMMON_INST (
    .DMONITOROUT (delay_DMONITOROUT),
    .DRPDO (delay_DRPDO),
    .DRPRDY (delay_DRPRDY),
    .PLL0FBCLKLOST (delay_PLL0FBCLKLOST),
    .PLL0LOCK (delay_PLL0LOCK),
    .PLL0OUTCLK (delay_PLL0OUTCLK),
    .PLL0OUTREFCLK (delay_PLL0OUTREFCLK),
    .PLL0REFCLKLOST (delay_PLL0REFCLKLOST),
    .PLL1FBCLKLOST (delay_PLL1FBCLKLOST),
    .PLL1LOCK (delay_PLL1LOCK),
    .PLL1OUTCLK (delay_PLL1OUTCLK),
    .PLL1OUTREFCLK (delay_PLL1OUTREFCLK),
    .PLL1REFCLKLOST (delay_PLL1REFCLKLOST),
    .PMARSVDOUT (delay_PMARSVDOUT),
    .REFCLKOUTMONITOR0 (delay_REFCLKOUTMONITOR0),
    .REFCLKOUTMONITOR1 (delay_REFCLKOUTMONITOR1),
    .BGBYPASSB (delay_BGBYPASSB),
    .BGMONITORENB (delay_BGMONITORENB),
    .BGPDB (delay_BGPDB),
    .BGRCALOVRD (delay_BGRCALOVRD),
    .BGRCALOVRDENB (delay_BGRCALOVRDENB),
    .DRPADDR (delay_DRPADDR),
    .DRPCLK (delay_DRPCLK),
    .DRPDI (delay_DRPDI),
    .DRPEN (delay_DRPEN),
    .DRPWE (delay_DRPWE),
    .GTEASTREFCLK0 (delay_GTEASTREFCLK0),
    .GTEASTREFCLK1 (delay_GTEASTREFCLK1),
    .GTGREFCLK0 (delay_GTGREFCLK0),
    .GTGREFCLK1 (delay_GTGREFCLK1),
    .GTREFCLK0 (delay_GTREFCLK0),
    .GTREFCLK1 (delay_GTREFCLK1),
    .GTWESTREFCLK0 (delay_GTWESTREFCLK0),
    .GTWESTREFCLK1 (delay_GTWESTREFCLK1),
    .PLL0LOCKDETCLK (delay_PLL0LOCKDETCLK),
    .PLL0LOCKEN (delay_PLL0LOCKEN),
    .PLL0PD (delay_PLL0PD),
    .PLL0REFCLKSEL (delay_PLL0REFCLKSEL),
    .PLL0RESET (delay_PLL0RESET),
    .PLL1LOCKDETCLK (delay_PLL1LOCKDETCLK),
    .PLL1LOCKEN (delay_PLL1LOCKEN),
    .PLL1PD (delay_PLL1PD),
    .PLL1REFCLKSEL (delay_PLL1REFCLKSEL),
    .PLL1RESET (delay_PLL1RESET),
    .PLLRSVD1 (delay_PLLRSVD1),
    .PLLRSVD2 (delay_PLLRSVD2),
    .PMARSVD (delay_PMARSVD),
    .RCALENB (delay_RCALENB),
    .GSR (GSR)
  );

  specify
`ifdef XIL_TIMING // Simprim
    $period (posedge DRPCLK, 0:0:0, notifier);
    $period (negedge DRPCLK, 0:0:0, notifier);
    $period (posedge GTEASTREFCLK0, 0:0:0, notifier);
    $period (posedge GTEASTREFCLK1, 0:0:0, notifier);
    $period (posedge GTGREFCLK0, 0:0:0, notifier);
    $period (negedge GTGREFCLK0, 0:0:0, notifier);
    $period (posedge GTGREFCLK1, 0:0:0, notifier);
    $period (negedge GTGREFCLK1, 0:0:0, notifier);
    $period (posedge GTREFCLK0, 0:0:0, notifier);
    $period (posedge GTREFCLK1, 0:0:0, notifier);
    $period (posedge GTWESTREFCLK0, 0:0:0, notifier);
    $period (posedge GTWESTREFCLK1, 0:0:0, notifier);
    $period (posedge PLL0LOCKDETCLK, 0:0:0, notifier);
    $period (negedge PLL0LOCKDETCLK, 0:0:0, notifier);
    $period (posedge PLL0OUTCLK, 0:0:0, notifier);
    $period (posedge PLL1LOCKDETCLK, 0:0:0, notifier);
    $period (negedge PLL1LOCKDETCLK, 0:0:0, notifier);
    $period (posedge PLL1OUTCLK, 0:0:0, notifier);
    $period (posedge REFCLKOUTMONITOR0, 0:0:0, notifier);
    $period (posedge REFCLKOUTMONITOR1, 0:0:0, notifier);
    $setuphold (posedge DRPCLK, negedge DRPADDR, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPADDR);
    $setuphold (posedge DRPCLK, negedge DRPDI, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPDI);
    $setuphold (posedge DRPCLK, negedge DRPEN, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPEN);
    $setuphold (posedge DRPCLK, negedge DRPWE, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPWE);
    $setuphold (posedge DRPCLK, posedge DRPADDR, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPADDR);
    $setuphold (posedge DRPCLK, posedge DRPDI, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPDI);
    $setuphold (posedge DRPCLK, posedge DRPEN, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPEN);
    $setuphold (posedge DRPCLK, posedge DRPWE, 0:0:0, 0:0:0, notifier, drpclk_en_p, drpclk_en_p, delay_DRPCLK, delay_DRPWE);
    $setuphold (negedge DRPCLK, negedge DRPADDR, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPADDR);
    $setuphold (negedge DRPCLK, negedge DRPDI, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPDI);
    $setuphold (negedge DRPCLK, negedge DRPEN, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPEN);
    $setuphold (negedge DRPCLK, negedge DRPWE, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPWE);
    $setuphold (negedge DRPCLK, posedge DRPADDR, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPADDR);
    $setuphold (negedge DRPCLK, posedge DRPDI, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPDI);
    $setuphold (negedge DRPCLK, posedge DRPEN, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPEN);
    $setuphold (negedge DRPCLK, posedge DRPWE, 0:0:0, 0:0:0, notifier, drpclk_en_n, drpclk_en_n, delay_DRPCLK, delay_DRPWE);
`endif

    ( DRPCLK *> DRPDO) = (0, 0);
    ( DRPCLK *> DRPRDY) = (0, 0);
    ( GTGREFCLK0 *> REFCLKOUTMONITOR0) = (0, 0);
    ( GTGREFCLK0 *> REFCLKOUTMONITOR1) = (0, 0);
    ( GTGREFCLK1 *> REFCLKOUTMONITOR0) = (0, 0);
    ( GTGREFCLK1 *> REFCLKOUTMONITOR1) = (0, 0);
    ( GTREFCLK0 *> REFCLKOUTMONITOR0) = (0, 0);
    ( GTREFCLK0 *> REFCLKOUTMONITOR1) = (0, 0);
    ( GTREFCLK1 *> REFCLKOUTMONITOR0) = (0, 0);
    ( GTREFCLK1 *> REFCLKOUTMONITOR1) = (0, 0);

    specparam PATHPULSE$ = 0;
  endspecify
endmodule
`endcelldefine
