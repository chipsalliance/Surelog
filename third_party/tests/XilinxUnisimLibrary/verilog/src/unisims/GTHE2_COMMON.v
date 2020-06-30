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
// /__/   /\       Filename    : GTHE2_COMMON.uniprim.v
// \  \  /  \ 
//  \__\/\__ \                    
//                                 
//  Revision:		1.0
//  Initial version
//  09/22/11 - 624065 - YML update
//  12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//  06/12/12 - 664920 - YML update
//  01/18/13 - 695630 - added drp monitor
//  08/29/14 - 821138 - add negedge specify section for IS_INVERTED*CLK*
///////////////////////////////////////////////////////

`timescale 1 ps / 1 ps 
`celldefine
    
module GTHE2_COMMON (
  DRPDO,
  DRPRDY,
  PMARSVDOUT,
  QPLLDMONITOR,
  QPLLFBCLKLOST,
  QPLLLOCK,
  QPLLOUTCLK,
  QPLLOUTREFCLK,
  QPLLREFCLKLOST,
  REFCLKOUTMONITOR,

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
  GTGREFCLK,
  GTNORTHREFCLK0,
  GTNORTHREFCLK1,
  GTREFCLK0,
  GTREFCLK1,
  GTSOUTHREFCLK0,
  GTSOUTHREFCLK1,
  PMARSVD,
  QPLLLOCKDETCLK,
  QPLLLOCKEN,
  QPLLOUTRESET,
  QPLLPD,
  QPLLREFCLKSEL,
  QPLLRESET,
  QPLLRSVD1,
  QPLLRSVD2,
  RCALENB
);

  `ifdef XIL_TIMING //Simprim 
  parameter LOC = "UNPLACED";
  `endif
  parameter [63:0] BIAS_CFG = 64'h0000040000001000;
  parameter [31:0] COMMON_CFG = 32'h0000001C;
  parameter [0:0] IS_DRPCLK_INVERTED = 1'b0;
  parameter [0:0] IS_GTGREFCLK_INVERTED = 1'b0;
  parameter [0:0] IS_QPLLLOCKDETCLK_INVERTED = 1'b0;
  parameter [26:0] QPLL_CFG = 27'h0480181;
  parameter [3:0] QPLL_CLKOUT_CFG = 4'b0000;
  parameter [5:0] QPLL_COARSE_FREQ_OVRD = 6'b010000;
  parameter [0:0] QPLL_COARSE_FREQ_OVRD_EN = 1'b0;
  parameter [9:0] QPLL_CP = 10'b0000011111;
  parameter [0:0] QPLL_CP_MONITOR_EN = 1'b0;
  parameter [0:0] QPLL_DMONITOR_SEL = 1'b0;
  parameter [9:0] QPLL_FBDIV = 10'b0000000000;
  parameter [0:0] QPLL_FBDIV_MONITOR_EN = 1'b0;
  parameter [0:0] QPLL_FBDIV_RATIO = 1'b0;
  parameter [23:0] QPLL_INIT_CFG = 24'h000006;
  parameter [15:0] QPLL_LOCK_CFG = 16'h01E8;
  parameter [3:0] QPLL_LPF = 4'b1111;
  parameter integer QPLL_REFCLK_DIV = 2;
  parameter [0:0] QPLL_RP_COMP = 1'b0;
  parameter [1:0] QPLL_VTRL_RESET = 2'b00;
  parameter [1:0] RCAL_CFG = 2'b00;
  parameter [15:0] RSVD_ATTR0 = 16'h0000;
  parameter [15:0] RSVD_ATTR1 = 16'h0000;
  parameter [2:0] SIM_QPLLREFCLK_SEL = 3'b001;
  parameter SIM_RESET_SPEEDUP = "TRUE";
  parameter SIM_VERSION = "1.1";
  
  localparam in_delay = 0;
  localparam out_delay = 0;
  localparam INCLK_DELAY = 0;
  localparam OUTCLK_DELAY = 0;

  output DRPRDY;
  output QPLLFBCLKLOST;
  output QPLLLOCK;
  output QPLLOUTCLK;
  output QPLLOUTREFCLK;
  output QPLLREFCLKLOST;
  output REFCLKOUTMONITOR;
  output [15:0] DRPDO;
  output [15:0] PMARSVDOUT;
  output [7:0] QPLLDMONITOR;

  input BGBYPASSB;
  input BGMONITORENB;
  input BGPDB;
  input BGRCALOVRDENB;
  input DRPCLK;
  input DRPEN;
  input DRPWE;
  input GTGREFCLK;
  input GTNORTHREFCLK0;
  input GTNORTHREFCLK1;
  input GTREFCLK0;
  input GTREFCLK1;
  input GTSOUTHREFCLK0;
  input GTSOUTHREFCLK1;
  input QPLLLOCKDETCLK;
  input QPLLLOCKEN;
  input QPLLOUTRESET;
  input QPLLPD;
  input QPLLRESET;
  input RCALENB;
  input [15:0] DRPDI;
  input [15:0] QPLLRSVD1;
  input [2:0] QPLLREFCLKSEL;
  input [4:0] BGRCALOVRD;
  input [4:0] QPLLRSVD2;
  input [7:0] DRPADDR;
  input [7:0] PMARSVD;

  reg SIM_RESET_SPEEDUP_BINARY;
  reg SIM_VERSION_BINARY;
  reg [0:0] QPLL_COARSE_FREQ_OVRD_EN_BINARY;
  reg [0:0] QPLL_CP_MONITOR_EN_BINARY;
  reg [0:0] QPLL_DMONITOR_SEL_BINARY;
  reg [0:0] QPLL_FBDIV_MONITOR_EN_BINARY;
  reg [0:0] QPLL_FBDIV_RATIO_BINARY;
  reg [0:0] QPLL_RP_COMP_BINARY;
  reg [1:0] QPLL_VTRL_RESET_BINARY;
  reg [1:0] RCAL_CFG_BINARY;
  reg [2:0] SIM_QPLLREFCLK_SEL_BINARY;
  reg [3:0] QPLL_CLKOUT_CFG_BINARY;
  reg [3:0] QPLL_LPF_BINARY;
  reg [4:0] QPLL_REFCLK_DIV_BINARY;
  reg [5:0] QPLL_COARSE_FREQ_OVRD_BINARY;
  reg [9:0] QPLL_CP_BINARY;
  reg [9:0] QPLL_FBDIV_BINARY;

  tri0 GSR = glbl.GSR;
  reg notifier;

  initial begin
    case (QPLL_REFCLK_DIV)
      2 : QPLL_REFCLK_DIV_BINARY = 5'b00000;
      1 : QPLL_REFCLK_DIV_BINARY = 5'b10000;
      3 : QPLL_REFCLK_DIV_BINARY = 5'b00001;
      4 : QPLL_REFCLK_DIV_BINARY = 5'b00010;
      5 : QPLL_REFCLK_DIV_BINARY = 5'b00011;
      6 : QPLL_REFCLK_DIV_BINARY = 5'b00101;
      8 : QPLL_REFCLK_DIV_BINARY = 5'b00110;
      10 : QPLL_REFCLK_DIV_BINARY = 5'b00111;
      12 : QPLL_REFCLK_DIV_BINARY = 5'b01101;
      16 : QPLL_REFCLK_DIV_BINARY = 5'b01110;
      20 : QPLL_REFCLK_DIV_BINARY = 5'b01111;
      default : begin
        $display("Attribute Syntax Error : The Attribute QPLL_REFCLK_DIV on GTHE2_COMMON instance %m is set to %d.  Legal values for this attribute are 1 to 20.", QPLL_REFCLK_DIV, 2);
        #1 $finish;
      end
    endcase

    case (SIM_RESET_SPEEDUP)
      "TRUE" : SIM_RESET_SPEEDUP_BINARY = 0;
      "FALSE" : SIM_RESET_SPEEDUP_BINARY = 0;
      default : begin
        $display("Attribute Syntax Error : The Attribute SIM_RESET_SPEEDUP on GTHE2_COMMON instance %m is set to %s.  Legal values for this attribute are TRUE, or FALSE.", SIM_RESET_SPEEDUP);
        #1 $finish;
      end
    endcase
 case (SIM_VERSION)
      "1.1" : SIM_VERSION_BINARY = 0;
      "1.0" : SIM_VERSION_BINARY = 0;
      "2.0" : SIM_VERSION_BINARY = 0;
      default : begin
        $display("Attribute Syntax Error : The Attribute SIM_VERSION on GTHE2_CHANNEL instance %m is set to %s.  Legal values for this attribute are 1.1, 1.0, or 2.0.", SIM_VERSION);
        #1 $finish;
      end
endcase


    if ((QPLL_CLKOUT_CFG >= 4'b0000) && (QPLL_CLKOUT_CFG <= 4'b1111))
      QPLL_CLKOUT_CFG_BINARY = QPLL_CLKOUT_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute QPLL_CLKOUT_CFG on GTHE2_COMMON instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", QPLL_CLKOUT_CFG);
      #1 $finish;
    end

    if ((QPLL_COARSE_FREQ_OVRD >= 6'b000000) && (QPLL_COARSE_FREQ_OVRD <= 6'b111111))
      QPLL_COARSE_FREQ_OVRD_BINARY = QPLL_COARSE_FREQ_OVRD;
    else begin
      $display("Attribute Syntax Error : The Attribute QPLL_COARSE_FREQ_OVRD on GTHE2_COMMON instance %m is set to %b.  Legal values for this attribute are 6'b000000 to 6'b111111.", QPLL_COARSE_FREQ_OVRD);
      #1 $finish;
    end

    if ((QPLL_COARSE_FREQ_OVRD_EN >= 1'b0) && (QPLL_COARSE_FREQ_OVRD_EN <= 1'b1))
      QPLL_COARSE_FREQ_OVRD_EN_BINARY = QPLL_COARSE_FREQ_OVRD_EN;
    else begin
      $display("Attribute Syntax Error : The Attribute QPLL_COARSE_FREQ_OVRD_EN on GTHE2_COMMON instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", QPLL_COARSE_FREQ_OVRD_EN);
      #1 $finish;
    end

    if ((QPLL_CP >= 10'b0000000000) && (QPLL_CP <= 10'b1111111111))
      QPLL_CP_BINARY = QPLL_CP;
    else begin
      $display("Attribute Syntax Error : The Attribute QPLL_CP on GTHE2_COMMON instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", QPLL_CP);
      #1 $finish;
    end

    if ((QPLL_CP_MONITOR_EN >= 1'b0) && (QPLL_CP_MONITOR_EN <= 1'b1))
      QPLL_CP_MONITOR_EN_BINARY = QPLL_CP_MONITOR_EN;
    else begin
      $display("Attribute Syntax Error : The Attribute QPLL_CP_MONITOR_EN on GTHE2_COMMON instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", QPLL_CP_MONITOR_EN);
      #1 $finish;
    end

    if ((QPLL_DMONITOR_SEL >= 1'b0) && (QPLL_DMONITOR_SEL <= 1'b1))
      QPLL_DMONITOR_SEL_BINARY = QPLL_DMONITOR_SEL;
    else begin
      $display("Attribute Syntax Error : The Attribute QPLL_DMONITOR_SEL on GTHE2_COMMON instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", QPLL_DMONITOR_SEL);
      #1 $finish;
    end

    if ((QPLL_FBDIV >= 10'b0000000000) && (QPLL_FBDIV <= 10'b1111111111))
      QPLL_FBDIV_BINARY = QPLL_FBDIV;
    else begin
      $display("Attribute Syntax Error : The Attribute QPLL_FBDIV on GTHE2_COMMON instance %m is set to %b.  Legal values for this attribute are 10'b0000000000 to 10'b1111111111.", QPLL_FBDIV);
      #1 $finish;
    end

    if ((QPLL_FBDIV_MONITOR_EN >= 1'b0) && (QPLL_FBDIV_MONITOR_EN <= 1'b1))
      QPLL_FBDIV_MONITOR_EN_BINARY = QPLL_FBDIV_MONITOR_EN;
    else begin
      $display("Attribute Syntax Error : The Attribute QPLL_FBDIV_MONITOR_EN on GTHE2_COMMON instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", QPLL_FBDIV_MONITOR_EN);
      #1 $finish;
    end

    if ((QPLL_FBDIV_RATIO >= 1'b0) && (QPLL_FBDIV_RATIO <= 1'b1))
      QPLL_FBDIV_RATIO_BINARY = QPLL_FBDIV_RATIO;
    else begin
      $display("Attribute Syntax Error : The Attribute QPLL_FBDIV_RATIO on GTHE2_COMMON instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", QPLL_FBDIV_RATIO);
      #1 $finish;
    end

    if ((QPLL_LPF >= 4'b0000) && (QPLL_LPF <= 4'b1111))
      QPLL_LPF_BINARY = QPLL_LPF;
    else begin
      $display("Attribute Syntax Error : The Attribute QPLL_LPF on GTHE2_COMMON instance %m is set to %b.  Legal values for this attribute are 4'b0000 to 4'b1111.", QPLL_LPF);
      #1 $finish;
    end

    if ((QPLL_RP_COMP >= 1'b0) && (QPLL_RP_COMP <= 1'b1))
      QPLL_RP_COMP_BINARY = QPLL_RP_COMP;
    else begin
      $display("Attribute Syntax Error : The Attribute QPLL_RP_COMP on GTHE2_COMMON instance %m is set to %b.  Legal values for this attribute are 1'b0 to 1'b1.", QPLL_RP_COMP);
      #1 $finish;
    end

    if ((QPLL_VTRL_RESET >= 2'b00) && (QPLL_VTRL_RESET <= 2'b11))
      QPLL_VTRL_RESET_BINARY = QPLL_VTRL_RESET;
    else begin
      $display("Attribute Syntax Error : The Attribute QPLL_VTRL_RESET on GTHE2_COMMON instance %m is set to %b.  Legal values for this attribute are 2'b00 to 2'b11.", QPLL_VTRL_RESET);
      #1 $finish;
    end

    if ((RCAL_CFG >= 2'b00) && (RCAL_CFG <= 2'b11))
      RCAL_CFG_BINARY = RCAL_CFG;
    else begin
      $display("Attribute Syntax Error : The Attribute RCAL_CFG on GTHE2_COMMON instance %m is set to %b.  Legal values for this attribute are 2'b00 to 2'b11.", RCAL_CFG);
      #1 $finish;
    end

    if ((SIM_QPLLREFCLK_SEL >= 3'b0) && (SIM_QPLLREFCLK_SEL <= 3'b111))
      SIM_QPLLREFCLK_SEL_BINARY = SIM_QPLLREFCLK_SEL;
    else begin
      $display("Attribute Syntax Error : The Attribute SIM_QPLLREFCLK_SEL on GTHE2_COMMON instance %m is set to %b.  Legal values for this attribute are 3'b0 to 3'b111.", SIM_QPLLREFCLK_SEL);
      #1 $finish;
    end

  end

  wire [15:0] delay_DRPDO;
  wire [15:0] delay_PMARSVDOUT;
  wire [7:0] delay_QPLLDMONITOR;
  wire delay_DRPRDY;
  wire delay_QPLLFBCLKLOST;
  wire delay_QPLLLOCK;
  wire delay_QPLLOUTCLK;
  wire delay_QPLLOUTREFCLK;
  wire delay_QPLLREFCLKLOST;
  wire delay_REFCLKOUTMONITOR;

  wire [15:0] delay_DRPDI;
  wire [15:0] delay_QPLLRSVD1;
  wire [2:0] delay_QPLLREFCLKSEL;
  wire [4:0] delay_BGRCALOVRD;
  wire [4:0] delay_QPLLRSVD2;
  wire [7:0] delay_DRPADDR;
  wire [7:0] delay_PMARSVD;
  wire delay_BGBYPASSB;
  wire delay_BGMONITORENB;
  wire delay_BGPDB;
  wire delay_BGRCALOVRDENB;
  wire delay_DRPCLK;
  wire delay_DRPEN;
  wire delay_DRPWE;
  wire delay_GTGREFCLK;
  wire delay_GTNORTHREFCLK0;
  wire delay_GTNORTHREFCLK1;
  wire delay_GTREFCLK0;
  wire delay_GTREFCLK1;
  wire delay_GTSOUTHREFCLK0;
  wire delay_GTSOUTHREFCLK1;
  wire delay_QPLLLOCKDETCLK;
  wire delay_QPLLLOCKEN;
  wire delay_QPLLOUTRESET;
  wire delay_QPLLPD;
  wire delay_QPLLRESET;
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
   reg [0:0] IS_GTGREFCLK_INVERTED_REG = IS_GTGREFCLK_INVERTED;
   reg [0:0] IS_QPLLLOCKDETCLK_INVERTED_REG = IS_QPLLLOCKDETCLK_INVERTED;
   
   
  assign  QPLLOUTCLK = delay_QPLLOUTCLK;
  assign  REFCLKOUTMONITOR = delay_REFCLKOUTMONITOR;

  assign  DRPDO = delay_DRPDO;
  assign  DRPRDY = delay_DRPRDY;
  assign  PMARSVDOUT = delay_PMARSVDOUT;
  assign  QPLLDMONITOR = delay_QPLLDMONITOR;
  assign  QPLLFBCLKLOST = delay_QPLLFBCLKLOST;
  assign  QPLLLOCK = delay_QPLLLOCK;
  assign  QPLLOUTREFCLK = delay_QPLLOUTREFCLK;
  assign  QPLLREFCLKLOST = delay_QPLLREFCLKLOST;
  
`ifndef XIL_TIMING // unisim
  assign  delay_DRPCLK = DRPCLK ^ IS_DRPCLK_INVERTED_REG;
  assign  delay_GTGREFCLK = GTGREFCLK ^ IS_GTGREFCLK_INVERTED_REG;
  assign  delay_GTNORTHREFCLK0 = GTNORTHREFCLK0;
  assign  delay_GTNORTHREFCLK1 = GTNORTHREFCLK1;
  assign  delay_GTREFCLK0 = GTREFCLK0;
  assign  delay_GTREFCLK1 = GTREFCLK1;
  assign  delay_GTSOUTHREFCLK0 = GTSOUTHREFCLK0;
  assign  delay_GTSOUTHREFCLK1 = GTSOUTHREFCLK1;
  assign  delay_QPLLLOCKDETCLK = QPLLLOCKDETCLK ^ IS_QPLLLOCKDETCLK_INVERTED_REG;

  assign  delay_BGBYPASSB = BGBYPASSB;
  assign  delay_BGMONITORENB = BGMONITORENB;
  assign  delay_BGPDB = BGPDB;
  assign  delay_BGRCALOVRD = BGRCALOVRD;
  assign  delay_BGRCALOVRDENB = BGRCALOVRDENB;
  assign  delay_DRPADDR = DRPADDR;
  assign  delay_DRPDI = DRPDI;
  assign  delay_DRPEN = DRPEN;
  assign  delay_DRPWE = DRPWE;
  assign  delay_PMARSVD = PMARSVD;
  assign  delay_QPLLLOCKEN = QPLLLOCKEN;
  assign  delay_QPLLOUTRESET = QPLLOUTRESET;
  assign  delay_QPLLPD = QPLLPD;
  assign  delay_QPLLREFCLKSEL = QPLLREFCLKSEL;
  assign  delay_QPLLRESET = QPLLRESET;
  assign  delay_QPLLRSVD1 = QPLLRSVD1;
  assign  delay_QPLLRSVD2 = QPLLRSVD2;
  assign  delay_RCALENB = RCALENB;
`endif //  `ifndef XIL_TIMING

`ifdef XIL_TIMING //Simprim
  assign delay_BGBYPASSB = BGBYPASSB;
  assign delay_BGMONITORENB = BGMONITORENB;
  assign delay_BGPDB = BGPDB;
  assign delay_BGRCALOVRD = BGRCALOVRD;
  assign delay_BGRCALOVRDENB = BGRCALOVRDENB;
  assign delay_GTGREFCLK = GTGREFCLK;
  assign delay_GTNORTHREFCLK0 = GTNORTHREFCLK0;
  assign delay_GTNORTHREFCLK1 = GTNORTHREFCLK1;
  assign delay_GTREFCLK0 = GTREFCLK0;
  assign delay_GTREFCLK1 = GTREFCLK1;
  assign delay_GTSOUTHREFCLK0 = GTSOUTHREFCLK0;
  assign delay_GTSOUTHREFCLK1 = GTSOUTHREFCLK1;
  assign delay_PMARSVD = PMARSVD;
  assign delay_QPLLLOCKDETCLK = QPLLLOCKDETCLK;
  assign delay_QPLLLOCKEN = QPLLLOCKEN;
  assign delay_QPLLOUTRESET = QPLLOUTRESET;
  assign delay_QPLLPD = QPLLPD;
  assign delay_QPLLREFCLKSEL = QPLLREFCLKSEL;
  assign delay_QPLLRESET = QPLLRESET;
  assign delay_QPLLRSVD1 = QPLLRSVD1;
  assign delay_QPLLRSVD2 = QPLLRSVD2;
  assign delay_RCALENB = RCALENB;

  wire drpclk_en_p;
  wire drpclk_en_n;

  assign drpclk_en_p = ~IS_DRPCLK_INVERTED;
  assign drpclk_en_n = IS_DRPCLK_INVERTED;
`endif

  B_GTHE2_COMMON #(
    .BIAS_CFG (BIAS_CFG),
    .COMMON_CFG (COMMON_CFG),
    .QPLL_CFG (QPLL_CFG),
    .QPLL_CLKOUT_CFG (QPLL_CLKOUT_CFG),
    .QPLL_COARSE_FREQ_OVRD (QPLL_COARSE_FREQ_OVRD),
    .QPLL_COARSE_FREQ_OVRD_EN (QPLL_COARSE_FREQ_OVRD_EN),
    .QPLL_CP (QPLL_CP),
    .QPLL_CP_MONITOR_EN (QPLL_CP_MONITOR_EN),
    .QPLL_DMONITOR_SEL (QPLL_DMONITOR_SEL),
    .QPLL_FBDIV (QPLL_FBDIV),
    .QPLL_FBDIV_MONITOR_EN (QPLL_FBDIV_MONITOR_EN),
    .QPLL_FBDIV_RATIO (QPLL_FBDIV_RATIO),
    .QPLL_INIT_CFG (QPLL_INIT_CFG),
    .QPLL_LOCK_CFG (QPLL_LOCK_CFG),
    .QPLL_LPF (QPLL_LPF),
    .QPLL_REFCLK_DIV (QPLL_REFCLK_DIV),
    .QPLL_RP_COMP (QPLL_RP_COMP),
    .QPLL_VTRL_RESET (QPLL_VTRL_RESET),
    .RCAL_CFG (RCAL_CFG),
    .RSVD_ATTR0 (RSVD_ATTR0),
    .RSVD_ATTR1 (RSVD_ATTR1),
    .SIM_QPLLREFCLK_SEL (SIM_QPLLREFCLK_SEL),
    .SIM_RESET_SPEEDUP (SIM_RESET_SPEEDUP),
    .SIM_VERSION (SIM_VERSION))

    B_GTHE2_COMMON_INST (
    .DRPDO (delay_DRPDO),
    .DRPRDY (delay_DRPRDY),
    .PMARSVDOUT (delay_PMARSVDOUT),
    .QPLLDMONITOR (delay_QPLLDMONITOR),
    .QPLLFBCLKLOST (delay_QPLLFBCLKLOST),
    .QPLLLOCK (delay_QPLLLOCK),
    .QPLLOUTCLK (delay_QPLLOUTCLK),
    .QPLLOUTREFCLK (delay_QPLLOUTREFCLK),
    .QPLLREFCLKLOST (delay_QPLLREFCLKLOST),
    .REFCLKOUTMONITOR (delay_REFCLKOUTMONITOR),
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
    .GTGREFCLK (delay_GTGREFCLK),
    .GTNORTHREFCLK0 (delay_GTNORTHREFCLK0),
    .GTNORTHREFCLK1 (delay_GTNORTHREFCLK1),
    .GTREFCLK0 (delay_GTREFCLK0),
    .GTREFCLK1 (delay_GTREFCLK1),
    .GTSOUTHREFCLK0 (delay_GTSOUTHREFCLK0),
    .GTSOUTHREFCLK1 (delay_GTSOUTHREFCLK1),
    .PMARSVD (delay_PMARSVD),
    .QPLLLOCKDETCLK (delay_QPLLLOCKDETCLK),
    .QPLLLOCKEN (delay_QPLLLOCKEN),
    .QPLLOUTRESET (delay_QPLLOUTRESET),
    .QPLLPD (delay_QPLLPD),
    .QPLLREFCLKSEL (delay_QPLLREFCLKSEL),
    .QPLLRESET (delay_QPLLRESET),
    .QPLLRSVD1 (delay_QPLLRSVD1),
    .QPLLRSVD2 (delay_QPLLRSVD2),
    .RCALENB (delay_RCALENB),
    .GSR(GSR)
  );

  specify
`ifdef XIL_TIMING // Simprim
    $period (posedge DRPCLK, 0:0:0, notifier);
    $period (negedge DRPCLK, 0:0:0, notifier);
    $period (posedge GTGREFCLK, 0:0:0, notifier);
    $period (negedge GTGREFCLK, 0:0:0, notifier);
    $period (posedge GTNORTHREFCLK0, 0:0:0, notifier);
    $period (posedge GTNORTHREFCLK1, 0:0:0, notifier);
    $period (posedge GTREFCLK0, 0:0:0, notifier);
    $period (posedge GTREFCLK1, 0:0:0, notifier);
    $period (posedge GTSOUTHREFCLK0, 0:0:0, notifier);
    $period (posedge GTSOUTHREFCLK1, 0:0:0, notifier);
    $period (posedge QPLLLOCKDETCLK, 0:0:0, notifier);
    $period (negedge QPLLLOCKDETCLK, 0:0:0, notifier);
    $period (posedge QPLLOUTCLK, 0:0:0, notifier);
    $period (posedge REFCLKOUTMONITOR, 0:0:0, notifier);
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
    ( GTGREFCLK *> REFCLKOUTMONITOR) = (0, 0);
    ( GTNORTHREFCLK0 *> REFCLKOUTMONITOR) = (0, 0);
    ( GTNORTHREFCLK1 *> REFCLKOUTMONITOR) = (0, 0);
    ( GTREFCLK0 *> REFCLKOUTMONITOR) = (0, 0);
    ( GTREFCLK1 *> REFCLKOUTMONITOR) = (0, 0);
    ( GTSOUTHREFCLK0 *> REFCLKOUTMONITOR) = (0, 0);
    ( GTSOUTHREFCLK1 *> REFCLKOUTMONITOR) = (0, 0);

    specparam PATHPULSE$ = 0;
  endspecify
endmodule

`endcelldefine
