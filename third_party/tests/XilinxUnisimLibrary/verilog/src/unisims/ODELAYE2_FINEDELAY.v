///////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2011 Xilinx, Inc.
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
// \   \   \/     Version : 13.0
//  \   \         Description : Xilinx Functional and Timing Simulation Library Component
//  /   /                  Onput Fixed or Variable Delay Element with Fine Adjustment.
// /___/   /\     Filename : ODELAYE2_FINEDELAY.v
// \   \  /  \    Timestamp : Tue Feb 15 15:52:17 PST 2011 
//  \___\/\___\
//
// Revision:
//    02/15/11 - Initial version.
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//    10/22/14 - Added #1 to $finish (CR 808642).
// End Revision

`timescale  1 ps / 1 ps

`celldefine

module ODELAYE2_FINEDELAY (
  CNTVALUEOUT,
  DATAOUT,

  C,
  CE,
  CINVCTRL,
  CLKIN,
  CNTVALUEIN,
  INC,
  LD,
  LDPIPEEN,
  ODATAIN,
  OFDLY,
  REGRST
);

    parameter CINVCTRL_SEL = "FALSE";
    parameter DELAY_SRC = "ODATAIN";
    parameter FINEDELAY = "BYPASS";
    parameter HIGH_PERFORMANCE_MODE    = "FALSE";
    parameter [0:0] IS_C_INVERTED = 1'b0;
    parameter [0:0] IS_ODATAIN_INVERTED = 1'b0;
    parameter ODELAY_TYPE  = "FIXED";
    parameter integer ODELAY_VALUE = 0;
    parameter PIPE_SEL = "FALSE";
    parameter real REFCLK_FREQUENCY = 200.0;
    parameter SIGNAL_PATTERN    = "DATA";


`ifdef XIL_TIMING
    parameter LOC = "UNPLACED";
    parameter integer SIM_DELAY_D = 0;
    localparam DELAY_D = (ODELAY_TYPE == "VARIABLE") ? SIM_DELAY_D : 0;
`endif // ifdef XIL_TIMING

`ifndef XIL_TIMING
    integer DELAY_D=0;
`endif // ifndef XIL_TIMING

    output [4:0] CNTVALUEOUT;
    output DATAOUT;

    input C;
    input CE;
    input CINVCTRL;
    input CLKIN;
    input [4:0] CNTVALUEIN;
    input INC;
    input LD;
    input LDPIPEEN;
    input ODATAIN;
    input [2:0] OFDLY;
    input REGRST;


    tri0  GSR = glbl.GSR;

    real  CALC_TAPDELAY_RD ; // regular tap delay
    real  CALC_TAPDELAY_FD ; // fine tap delay
    real  INIT_DELAY_RD;
    real  INIT_DELAY_FD;

//------------------- constants ------------------------------------

    localparam MAX_DELAY_COUNT = 31; 
    localparam MIN_DELAY_COUNT = 0; 

    localparam MAX_REFCLK_FREQUENCYL = 210.0;
    localparam MIN_REFCLK_FREQUENCYL = 190.0;

    localparam MAX_REFCLK_FREQUENCYH = 410.0;
    localparam MIN_REFCLK_FREQUENCYH = 290.0;


//------------------- variable declaration -------------------------

    integer odelay_count;
    integer CNTVALUEIN_INTEGER;
    reg [4:0] cntvalueout_pre;

    reg notifier;

    reg data_mux = 0;
    reg tap_out_rd   = 0;
    reg tap_out_fd   = 0;
    reg tap_out_final   = 0;
    reg DATAOUT_reg   = 0;

    wire delay_chain_0,  delay_chain_1,  delay_chain_2,  delay_chain_3,
         delay_chain_4,  delay_chain_5,  delay_chain_6,  delay_chain_7,
         delay_chain_8,  delay_chain_9,  delay_chain_10, delay_chain_11,
         delay_chain_12, delay_chain_13, delay_chain_14, delay_chain_15,
         delay_chain_16, delay_chain_17, delay_chain_18, delay_chain_19,
         delay_chain_20, delay_chain_21, delay_chain_22, delay_chain_23,
         delay_chain_24, delay_chain_25, delay_chain_26, delay_chain_27,
         delay_chain_28, delay_chain_29, delay_chain_30, delay_chain_31;

    wire fine_delay_0, fine_delay_1, fine_delay_2, fine_delay_3,  fine_delay_4, fine_delay_5;

    reg  c_in;
    wire c_in_pre,delay_c;
    wire ce_in,delay_ce;
    wire cinvctrl_in,delay_cinvctrl;
    wire clkin_in,delay_clkin;
    wire [4:0] cntvaluein_in,delay_cntvaluein;
    wire odatain_in,delay_odatain;
    wire ofdly_in,delay_ofdly;
    wire gsr_in;
    wire inc_in,delay_inc;
    wire ld_in,delay_ld;
    wire ldpipeen_in,delay_ldpipeen;
    wire regrst_in,delay_regrst;

   reg [4:0] qcntvalueout_reg = 5'b0;
   reg [4:0] qcntvalueout_mux = 5'b0;


//----------------------------------------------------------------------
//-------------------------------  Output ------------------------------
//----------------------------------------------------------------------
  generate
      case (FINEDELAY)
         "BYPASS"  : always @(tap_out_rd) tap_out_final = tap_out_rd;
         "ADD_DLY" : always @(tap_out_fd) tap_out_final = tap_out_fd;
      endcase
   endgenerate

// CR 587496
//    assign #INIT_DELAY DATAOUT = tap_out_final;
    always @(tap_out_final)
       DATAOUT_reg <= #INIT_DELAY_RD tap_out_final;

    assign DATAOUT = DATAOUT_reg;
    assign CNTVALUEOUT = cntvalueout_pre;

`ifndef XIL_TIMING
//----------------------------------------------------------------------
//-------------------------------  Input -------------------------------
//----------------------------------------------------------------------
    assign delay_c =  C;
    assign delay_ce = CE;
    assign delay_cntvaluein = CNTVALUEIN;
    assign delay_inc = INC;
    assign delay_ld = LD;
    assign delay_ldpipeen = LDPIPEEN;
    assign delay_regrst = REGRST;
`endif // ifndef XIL_TIMING
    assign delay_cinvctrl = CINVCTRL;
    assign delay_clkin = CLKIN;
    assign delay_odatain =  ODATAIN;
    assign delay_ofdly = OFDLY;
    assign gsr_in = GSR;

    assign c_in_pre = IS_C_INVERTED ^ delay_c;
    assign ce_in = delay_ce;
    assign cntvaluein_in = delay_cntvaluein;
    assign inc_in = delay_inc;
    assign ld_in = delay_ld;
    assign ldpipeen_in = delay_ldpipeen;
    assign regrst_in = delay_regrst;

    assign cinvctrl_in = delay_cinvctrl;
    assign clkin_in = delay_clkin;
    assign odatain_in = IS_ODATAIN_INVERTED ^ delay_odatain;
    assign ofdly_in = delay_ofdly;


//*** GLOBAL hidden GSR pin
    always @(gsr_in) begin
	if (gsr_in == 1'b1) begin
//   For simprims, the fixed Delay values are taken from the sdf.
            if (ODELAY_TYPE == "FIXED")
                assign odelay_count = 0;
            else
                assign odelay_count = ODELAY_VALUE;
        end
	else if (gsr_in == 1'b0) begin
	    deassign odelay_count;
	end
    end


//------------------------------------------------------------
//---------------------   Initialization  --------------------
//------------------------------------------------------------

    initial begin

        //-------- CINVCTRL_SEL check

        case (CINVCTRL_SEL)
            "TRUE", "FALSE" : ;
            default : begin
               $display("Attribute Syntax Error : The attribute CINVCTRL_SEL on ODELAYE2_FINEDELAY instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.",  CINVCTRL_SEL);
               #1 $finish;
            end
        endcase

        //-------- DELAY_SRC check

        if (DELAY_SRC != "ODATAIN" && DELAY_SRC != "CLKIN") begin
            $display("Attribute Syntax Error : The attribute DELAY_SRC on ODELAYE2_FINEDELAY instance %m is set to %s.  Legal values for this attribute are ODATAIN or CLKIN", DELAY_SRC);
            #1 $finish;
        end

        //-------- FINEDELAY check

        if (FINEDELAY != "BYPASS" && FINEDELAY != "ADD_DLY") begin
            $display("Attribute Syntax Error : The attribute FINEDELAY on ODELAYE2_FINEDELAY instance %m is set to %s.  Legal values for this attribute are BYPASS or ADD_DLY", FINEDELAY);
            #1 $finish;
        end

        //-------- HIGH_PERFORMANCE_MODE check

        case (HIGH_PERFORMANCE_MODE)
            "TRUE", "FALSE" : ;
            default : begin
               $display("Attribute Syntax Error : The attribute HIGH_PERFORMANCE_MODE on ODELAYE2_FINEDELAY instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.",  HIGH_PERFORMANCE_MODE);
               #1 $finish;
            end
        endcase


        //-------- ODELAY_TYPE check

        if (ODELAY_TYPE != "FIXED" && ODELAY_TYPE != "VARIABLE" && ODELAY_TYPE != "VAR_LOAD" && ODELAY_TYPE != "VAR_LOAD_PIPE") begin

            $display("Attribute Syntax Error : The attribute ODELAY_TYPE on ODELAYE2_FINEDELAY instance %m is set to %s.  Legal values for this attribute are FIXED, VARIABLE, VAR_LOAD or VAR_LOAD_PIPE", ODELAY_TYPE);
            #1 $finish;

        end


        //-------- ODELAY_VALUE check

        if (ODELAY_VALUE < MIN_DELAY_COUNT || ODELAY_VALUE > MAX_DELAY_COUNT) begin
            $display("Attribute Syntax Error : The attribute ODELAY_VALUE on ODELAYE2_FINEDELAY instance %m is set to %d.  Legal values for this attribute are 0, 1, 2, 3, .... or 31", ODELAY_VALUE);
            #1 $finish;

        end

        //-------- PIPE_SEL check

        case (PIPE_SEL)
            "TRUE", "FALSE" : ;
            default : begin
               $display("Attribute Syntax Error : The attribute PIPE_SEL on ODELAYE2_FINEDELAY instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.",  PIPE_SEL);
               #1 $finish;
            end
        endcase



        //-------- REFCLK_FREQUENCY check

        if ((REFCLK_FREQUENCY >= 190.0 && REFCLK_FREQUENCY <= 210.0) || 
	    (REFCLK_FREQUENCY >= 290.0 && REFCLK_FREQUENCY <= 310.0) || 
	    (REFCLK_FREQUENCY >=390.0 && REFCLK_FREQUENCY <= 410.0)) 
	      /*    */;
	else begin
            $display("Attribute Syntax Error : The attribute REFCLK_FREQUENCY on ODELAYE2_FINEDELAY instance %m is set to %f.  Legal values for this attribute are either between 190.0 and 210.0, or between 290.0 and 310.0 or between 390.0 and 410.0", REFCLK_FREQUENCY);
            #1 $finish;
        end


        //-------- SIGNAL_PATTERN check

        case (SIGNAL_PATTERN)
            "CLOCK", "DATA" : ;
            default : begin
               $display("Attribute Syntax Error : The attribute SIGNAL_PATTERN on ODELAYE2_FINEDELAY instance %m is set to %s.  Legal values for this attribute are DATA or CLOCK.",  SIGNAL_PATTERN);
               #1 $finish;
            end
        endcase

        //-------- CALC_TAPDELAY_RD check

        INIT_DELAY_RD = 600;  //regular delay
        INIT_DELAY_FD = 40;   //fine delay

    end // initial begin

    // CALC_TAPDELAY_RD value
    initial begin
        if ((REFCLK_FREQUENCY <= 410.0) && (REFCLK_FREQUENCY >= 390.0))
               begin
                        CALC_TAPDELAY_RD = 39;
                end
        else if ((REFCLK_FREQUENCY <= 310.0) && (REFCLK_FREQUENCY >= 290.0))
                begin
                        CALC_TAPDELAY_RD = 52;
                end
        else
                begin
                        CALC_TAPDELAY_RD = 78;
                end

        CALC_TAPDELAY_FD = 10;  //fine delay
    end

//----------------------------------------------------------------------
//------------------------ Dynamic clock inversion ---------------------
//----------------------------------------------------------------------
   generate
      case (CINVCTRL_SEL)
         "TRUE"  : always @(c_in_pre or cinvctrl_in) c_in = (cinvctrl_in ? ~c_in_pre : c_in_pre);
         "FALSE" : always @(c_in_pre) c_in = c_in_pre;
      endcase
   endgenerate
//----------------------------------------------------------------------
//------------------------      CNTVALUEOUT        ---------------------
//----------------------------------------------------------------------
    always @(odelay_count) begin
//  Fixed CNTVALUEOUT for when in FIXED mode because of simprim. 
       if(ODELAY_TYPE != "FIXED")
           assign cntvalueout_pre = odelay_count;
       else
           assign cntvalueout_pre = ODELAY_VALUE;
    end

//----------------------------------------------------------------------
//--------------------------  CNTVALUEIN LOAD --------------------------
//----------------------------------------------------------------------
    always @(posedge c_in) begin
       if (regrst_in == 1'b1) 
              qcntvalueout_reg = 5'b0;
       else if (regrst_in == 1'b0 && ldpipeen_in == 1'b1) begin
              qcntvalueout_reg =  CNTVALUEIN_INTEGER;
       end 
    end  // always @(posedge c_in)

   generate
      case (PIPE_SEL)
         "TRUE"  : always @(qcntvalueout_reg) qcntvalueout_mux   <= qcntvalueout_reg;
         "FALSE" : always @(CNTVALUEIN_INTEGER) qcntvalueout_mux   <= CNTVALUEIN_INTEGER;
      endcase
   endgenerate

//----------------------------------------------------------------------
//--------------------------  ODELAY_COUNT  ----------------------------
//----------------------------------------------------------------------
    always @(posedge c_in) begin

        if (ODELAY_TYPE == "VARIABLE" | ODELAY_TYPE == "VAR_LOAD" | ODELAY_TYPE == "VAR_LOAD_PIPE") begin
            if (ld_in == 1'b1) begin
                case (ODELAY_TYPE)
                        "VARIABLE" : odelay_count = ODELAY_VALUE;
                        "VAR_LOAD", "VAR_LOAD_PIPE" : odelay_count = qcntvalueout_mux;
                endcase
            end
            else if (ld_in == 1'b0 && ce_in == 1'b1) begin
                if (inc_in == 1'b1) begin
                    case (ODELAY_TYPE)
                        "VARIABLE", "VAR_LOAD", "VAR_LOAD_PIPE" : begin
                                        if (odelay_count < MAX_DELAY_COUNT)
                                        odelay_count = odelay_count + 1;
                                        else if (odelay_count == MAX_DELAY_COUNT)
                                        odelay_count = MIN_DELAY_COUNT;
                                     end
                    endcase
                end
                else if (inc_in == 1'b0) begin
                    case (ODELAY_TYPE)
                        "VARIABLE", "VAR_LOAD", "VAR_LOAD_PIPE" : begin
                                        if (odelay_count >  MIN_DELAY_COUNT)
                                        odelay_count = odelay_count - 1;
                                        else if (odelay_count == MIN_DELAY_COUNT)
                                        odelay_count = MAX_DELAY_COUNT;
                                     end
                    endcase
                end
            end
        end //
    end // always @ (posedge c_in)
  
    always @(cntvaluein_in or gsr_in) begin
                case (cntvaluein_in)
                        5'b00000 : assign CNTVALUEIN_INTEGER = 0;
                        5'b00001 : assign CNTVALUEIN_INTEGER = 1;
                        5'b00010 : assign CNTVALUEIN_INTEGER = 2;
                        5'b00011 : assign CNTVALUEIN_INTEGER = 3;
                        5'b00100 : assign CNTVALUEIN_INTEGER = 4;
                        5'b00101 : assign CNTVALUEIN_INTEGER = 5;
                        5'b00110 : assign CNTVALUEIN_INTEGER = 6;
                        5'b00111 : assign CNTVALUEIN_INTEGER = 7;
                        5'b01000 : assign CNTVALUEIN_INTEGER = 8;
                        5'b01001 : assign CNTVALUEIN_INTEGER = 9;
                        5'b01010 : assign CNTVALUEIN_INTEGER = 10;
                        5'b01011 : assign CNTVALUEIN_INTEGER = 11;
                        5'b01100 : assign CNTVALUEIN_INTEGER = 12;
                        5'b01101 : assign CNTVALUEIN_INTEGER = 13;
                        5'b01110 : assign CNTVALUEIN_INTEGER = 14;
                        5'b01111 : assign CNTVALUEIN_INTEGER = 15;
                        5'b10000 : assign CNTVALUEIN_INTEGER = 16;
                        5'b10001 : assign CNTVALUEIN_INTEGER = 17;
                        5'b10010 : assign CNTVALUEIN_INTEGER = 18;
                        5'b10011 : assign CNTVALUEIN_INTEGER = 19;
                        5'b10100 : assign CNTVALUEIN_INTEGER = 20;
                        5'b10101 : assign CNTVALUEIN_INTEGER = 21;
                        5'b10110 : assign CNTVALUEIN_INTEGER = 22;
                        5'b10111 : assign CNTVALUEIN_INTEGER = 23;
                        5'b11000 : assign CNTVALUEIN_INTEGER = 24;
                        5'b11001 : assign CNTVALUEIN_INTEGER = 25;
                        5'b11010 : assign CNTVALUEIN_INTEGER = 26;
                        5'b11011 : assign CNTVALUEIN_INTEGER = 27;
                        5'b11100 : assign CNTVALUEIN_INTEGER = 28;
                        5'b11101 : assign CNTVALUEIN_INTEGER = 29;
                        5'b11110 : assign CNTVALUEIN_INTEGER = 30;
                        5'b11111 : assign CNTVALUEIN_INTEGER = 31;
                endcase
    end

 
//*********************************************************
//*** SELECT IDATA signal
//*********************************************************

    always @(clkin_in or odatain_in) begin

        case (DELAY_SRC)

            "ODATAIN" : begin
                         data_mux <= odatain_in;
                        end
            "CLKIN"   : begin
                         data_mux <= clkin_in;
                       end
            default : begin
                          $display("Attribute Syntax Error : The attribute DELAY_SRC on ODELAYE2_FINEDELAY instance %m is set to %s.  Legal values for this attribute are CLKIN or ODATAIN", DELAY_SRC);
                          $finish;
                      end

        endcase // case(DELAY_SRC)

    end // always @(datain_in or idatain_in)

//*********************************************************
//*** DELAY IDATA signal
//*********************************************************
    assign #(DELAY_D)     delay_chain_0  = data_mux;
    assign #CALC_TAPDELAY_RD delay_chain_1  = delay_chain_0;
    assign #CALC_TAPDELAY_RD delay_chain_2  = delay_chain_1;
    assign #CALC_TAPDELAY_RD delay_chain_3  = delay_chain_2;
    assign #CALC_TAPDELAY_RD delay_chain_4  = delay_chain_3;
    assign #CALC_TAPDELAY_RD delay_chain_5  = delay_chain_4;
    assign #CALC_TAPDELAY_RD delay_chain_6  = delay_chain_5;
    assign #CALC_TAPDELAY_RD delay_chain_7  = delay_chain_6;
    assign #CALC_TAPDELAY_RD delay_chain_8  = delay_chain_7;
    assign #CALC_TAPDELAY_RD delay_chain_9  = delay_chain_8;
    assign #CALC_TAPDELAY_RD delay_chain_10 = delay_chain_9;
    assign #CALC_TAPDELAY_RD delay_chain_11 = delay_chain_10;
    assign #CALC_TAPDELAY_RD delay_chain_12 = delay_chain_11;
    assign #CALC_TAPDELAY_RD delay_chain_13 = delay_chain_12;
    assign #CALC_TAPDELAY_RD delay_chain_14 = delay_chain_13;
    assign #CALC_TAPDELAY_RD delay_chain_15 = delay_chain_14;
    assign #CALC_TAPDELAY_RD delay_chain_16 = delay_chain_15;
    assign #CALC_TAPDELAY_RD delay_chain_17 = delay_chain_16;
    assign #CALC_TAPDELAY_RD delay_chain_18 = delay_chain_17;
    assign #CALC_TAPDELAY_RD delay_chain_19 = delay_chain_18;
    assign #CALC_TAPDELAY_RD delay_chain_20 = delay_chain_19;
    assign #CALC_TAPDELAY_RD delay_chain_21 = delay_chain_20;
    assign #CALC_TAPDELAY_RD delay_chain_22 = delay_chain_21;
    assign #CALC_TAPDELAY_RD delay_chain_23 = delay_chain_22;
    assign #CALC_TAPDELAY_RD delay_chain_24 = delay_chain_23;
    assign #CALC_TAPDELAY_RD delay_chain_25 = delay_chain_24;
    assign #CALC_TAPDELAY_RD delay_chain_26 = delay_chain_25;
    assign #CALC_TAPDELAY_RD delay_chain_27 = delay_chain_26;
    assign #CALC_TAPDELAY_RD delay_chain_28 = delay_chain_27;
    assign #CALC_TAPDELAY_RD delay_chain_29 = delay_chain_28;
    assign #CALC_TAPDELAY_RD delay_chain_30 = delay_chain_29;
    assign #CALC_TAPDELAY_RD delay_chain_31 = delay_chain_30;

//*********************************************************
//*** assign delay
//*********************************************************
    always @(odelay_count) begin
        case (odelay_count)
            0:  assign tap_out_rd = delay_chain_0;
            1:  assign tap_out_rd = delay_chain_1;
            2:  assign tap_out_rd = delay_chain_2;
            3:  assign tap_out_rd = delay_chain_3;
            4:  assign tap_out_rd = delay_chain_4;
            5:  assign tap_out_rd = delay_chain_5;
            6:  assign tap_out_rd = delay_chain_6;
            7:  assign tap_out_rd = delay_chain_7;
            8:  assign tap_out_rd = delay_chain_8;
            9:  assign tap_out_rd = delay_chain_9;
            10: assign tap_out_rd = delay_chain_10;
            11: assign tap_out_rd = delay_chain_11;
            12: assign tap_out_rd = delay_chain_12;
            13: assign tap_out_rd = delay_chain_13;
            14: assign tap_out_rd = delay_chain_14;
            15: assign tap_out_rd = delay_chain_15;
            16: assign tap_out_rd = delay_chain_16;
            17: assign tap_out_rd = delay_chain_17;
            18: assign tap_out_rd = delay_chain_18;
            19: assign tap_out_rd = delay_chain_19;
            20: assign tap_out_rd = delay_chain_20;
            21: assign tap_out_rd = delay_chain_21;
            22: assign tap_out_rd = delay_chain_22;
            23: assign tap_out_rd = delay_chain_23;
            24: assign tap_out_rd = delay_chain_24;
            25: assign tap_out_rd = delay_chain_25;
            26: assign tap_out_rd = delay_chain_26;
            27: assign tap_out_rd = delay_chain_27;
            28: assign tap_out_rd = delay_chain_28;
            29: assign tap_out_rd = delay_chain_29;
            30: assign tap_out_rd = delay_chain_30;
            31: assign tap_out_rd = delay_chain_31;
            default:
                assign tap_out_rd = delay_chain_0;
        endcase
    end // always @ (odelay_count)

//*********************************************************
//*** FINE DELAY signal
//*********************************************************
    assign #(INIT_DELAY_FD)    fine_delay_0  = tap_out_rd;
    assign #CALC_TAPDELAY_FD   fine_delay_1  = fine_delay_0;
    assign #CALC_TAPDELAY_FD   fine_delay_2  = fine_delay_1;
    assign #CALC_TAPDELAY_FD   fine_delay_3  = fine_delay_2;
    assign #CALC_TAPDELAY_FD   fine_delay_4  = fine_delay_3;
    assign #CALC_TAPDELAY_FD   fine_delay_5  = fine_delay_4;

    always @(ofdly_in) begin
       case (ofdly_in)
          3'b000: assign tap_out_fd = fine_delay_0;
          3'b001: assign tap_out_fd = fine_delay_1;
          3'b010: assign tap_out_fd = fine_delay_2;
          3'b011: assign tap_out_fd = fine_delay_3;
          3'b100: assign tap_out_fd = fine_delay_4;
            default:
                assign tap_out_fd = 1'bx;
        endcase
    end // always @ (ofdly_in)


`ifdef XIL_TIMING
   wire c_en_n;
   wire c_en_p;
   assign c_en_n = IS_C_INVERTED;
   assign c_en_p = ~IS_C_INVERTED;

   wire c_d_en;
   wire o_d_en;

   assign c_d_en = (odelay_count == 0) && (ofdly_in == 0) && (DELAY_SRC == "CLKIN");
   assign o_d_en = (odelay_count == 0) && (ofdly_in == 0) && (DELAY_SRC == "ODATAIN");


//*** Timing Checks Start here

    always @(notifier) begin
        tap_out_rd <= 1'bx;
    end
`endif // ifdef XIL_TIMING

`ifdef XIL_TIMING
    specify

        ( C *> CNTVALUEOUT) = (0:0:0, 0:0:0);
        ( C => DATAOUT) = (0:0:0, 0:0:0);
        ( CINVCTRL *> CNTVALUEOUT) = (0:0:0, 0:0:0);
        ( CINVCTRL => DATAOUT) = (0:0:0, 0:0:0);
        if (c_d_en) ( CLKIN   => DATAOUT) = (0:0:0, 0:0:0);
        if (o_d_en) ( ODATAIN => DATAOUT) = (0:0:0, 0:0:0);

        $period (negedge C, 0:0:0, notifier);
        $period (posedge C, 0:0:0, notifier);

        $setuphold (posedge C, posedge CE,  0:0:0, 0:0:0, notifier, c_en_p, c_en_p, delay_c, delay_ce);
        $setuphold (posedge C, negedge CE,  0:0:0, 0:0:0, notifier, c_en_p, c_en_p, delay_c, delay_ce);
        $setuphold (posedge C, posedge INC, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, delay_c, delay_inc);
        $setuphold (posedge C, negedge INC, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, delay_c, delay_inc);
        $setuphold (posedge C, posedge LD, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, delay_c, delay_ld);
        $setuphold (posedge C, negedge LD, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, delay_c, delay_ld);
        $setuphold (posedge C, posedge CNTVALUEIN, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, delay_c, delay_cntvaluein);
        $setuphold (posedge C, negedge CNTVALUEIN, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, delay_c, delay_cntvaluein);
        $setuphold (posedge C, posedge LDPIPEEN, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, delay_c, delay_ldpipeen);
        $setuphold (posedge C, negedge LDPIPEEN, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, delay_c, delay_ldpipeen);
        $setuphold (posedge C, posedge REGRST, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, delay_c, delay_regrst);
        $setuphold (posedge C, negedge REGRST, 0:0:0, 0:0:0, notifier, c_en_p, c_en_p, delay_c, delay_regrst);

        $setuphold (negedge C, posedge CE,  0:0:0, 0:0:0, notifier, c_en_n, c_en_n, delay_c, delay_ce);
        $setuphold (negedge C, negedge CE,  0:0:0, 0:0:0, notifier, c_en_n, c_en_n, delay_c, delay_ce);
        $setuphold (negedge C, posedge INC, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, delay_c, delay_inc);
        $setuphold (negedge C, negedge INC, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, delay_c, delay_inc);
        $setuphold (negedge C, posedge LD, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, delay_c, delay_ld);
        $setuphold (negedge C, negedge LD, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, delay_c, delay_ld);
        $setuphold (negedge C, posedge CNTVALUEIN, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, delay_c, delay_cntvaluein);
        $setuphold (negedge C, negedge CNTVALUEIN, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, delay_c, delay_cntvaluein);
        $setuphold (negedge C, posedge LDPIPEEN, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, delay_c, delay_ldpipeen);
        $setuphold (negedge C, negedge LDPIPEEN, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, delay_c, delay_ldpipeen);
        $setuphold (negedge C, posedge REGRST, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, delay_c, delay_regrst);
        $setuphold (negedge C, negedge REGRST, 0:0:0, 0:0:0, notifier, c_en_n, c_en_n, delay_c, delay_regrst);


        specparam PATHPULSE$ = 0;

    endspecify
`endif // ifdef XIL_TIMING

endmodule // ODELAYE2_FINEDELAY

`endcelldefine
