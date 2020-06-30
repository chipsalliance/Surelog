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
// \   \   \/     Version : 13.1
//  \   \         Description : Xilinx Timing Simulation Library Component
//  /   /                  3-State Diffential Signaling I/O Buffer
// /___/   /\     Filename : IOBUFDS_DIFF_OUT_DCIEN.v
// \   \  /  \    Timestamp : Thu Apr 29 14:59:30 PDT 2010
//  \___\/\___\
//
// Revision:
//    04/29/10 - Initial version.
//    03/28/11 - CR 603466 fix
//    06/15/11 - CR 613347 -- made ouput logic_1 when IBUFDISABLE is active
//    08/31/11 - CR 623170 -- Tristate powergating support
//    09/20/11 - CR 625564 -- Fixed Tristate powergating polarity
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//    10/22/14 - Added #1 to $finish (CR 808642).
// End Revision

`timescale  1 ps / 1 ps


`celldefine

module IOBUFDS_DIFF_OUT_DCIEN (O, OB, IO, IOB, DCITERMDISABLE, I, IBUFDISABLE, TM, TS);

    parameter DIFF_TERM = "FALSE";
    parameter DQS_BIAS = "FALSE";
    parameter IBUF_LOW_PWR = "TRUE";
    parameter IOSTANDARD = "DEFAULT";
    parameter SIM_DEVICE = "7SERIES";
    parameter USE_IBUFDISABLE = "TRUE";
`ifdef XIL_TIMING
    parameter LOC = "UNPLACED";
`endif // `ifdef XIL_TIMING

    output O;
    output OB;
    inout  IO;
    inout  IOB;
    input  DCITERMDISABLE;
    input  I;
    input  IBUFDISABLE;
    input  TM;
    input  TS;

// define constants
  localparam MODULE_NAME = "IOBUFDS_DIFF_OUT_DCIEN";

    wire t1, t2, out_val, out_b_val;
    wire T_OR_IBUFDISABLE_1;
    wire T_OR_IBUFDISABLE_2;

    tri0 GTS = glbl.GTS;

    or O1 (t1, GTS, TM);
    bufif0 B1 (IO, I, t1);

    or O2 (t2, GTS, TS);
    notif0 N2 (IOB, I, t2);

    reg O_int, OB_int;
    reg DQS_BIAS_BINARY = 1'b0;


    initial begin
	
        case (DIFF_TERM)

            "TRUE", "FALSE" : ;
            default : begin
                          $display("Attribute Syntax Error : The attribute DIFF_TERM on IOBUFDS_DIFF_OUT_DCIEN instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.", DIFF_TERM);
                          #1 $finish;
                      end

        endcase // case(DIFF_TERM)
        case (IBUF_LOW_PWR)

            "FALSE", "TRUE" : ;
            default : begin
                          $display("Attribute Syntax Error : The attribute IBUF_LOW_PWR on IOBUFDS_DIFF_OUT_DCIEN instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.", IBUF_LOW_PWR);
                          #1 $finish;
                      end

        endcase
	case (DQS_BIAS)

            "TRUE"  : DQS_BIAS_BINARY <= #1 1'b1;
            "FALSE" : DQS_BIAS_BINARY <= #1 1'b0;
            default : begin
                          $display("Attribute Syntax Error : The attribute DQS_BIAS on IOBUFDS_DIFF_OUT_DCIEN instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.", DQS_BIAS);
                          #1 $finish;
                      end

        endcase

    if ((SIM_DEVICE != "7SERIES") &&
         (SIM_DEVICE != "ULTRASCALE") &&
         (SIM_DEVICE != "VERSAL_AI_CORE") &&
         (SIM_DEVICE != "VERSAL_AI_CORE_ES1") &&
         (SIM_DEVICE != "VERSAL_AI_CORE_ES2") &&
         (SIM_DEVICE != "VERSAL_AI_EDGE") &&
         (SIM_DEVICE != "VERSAL_AI_EDGE_ES1") &&
         (SIM_DEVICE != "VERSAL_AI_EDGE_ES2") &&
         (SIM_DEVICE != "VERSAL_AI_RF") &&
         (SIM_DEVICE != "VERSAL_AI_RF_ES1") &&
         (SIM_DEVICE != "VERSAL_AI_RF_ES2") &&
         (SIM_DEVICE != "VERSAL_HBM") &&
         (SIM_DEVICE != "VERSAL_HBM_ES1") &&
         (SIM_DEVICE != "VERSAL_HBM_ES2") &&
         (SIM_DEVICE != "VERSAL_PREMIUM") &&
         (SIM_DEVICE != "VERSAL_PREMIUM_ES1") &&
         (SIM_DEVICE != "VERSAL_PREMIUM_ES2") &&
         (SIM_DEVICE != "VERSAL_PRIME") &&
         (SIM_DEVICE != "VERSAL_PRIME_ES1") &&
         (SIM_DEVICE != "VERSAL_PRIME_ES2")) begin
      $display("Error: [Unisim %s-106] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are 7SERIES, ULTRASCALE, VERSAL_AI_CORE, VERSAL_AI_CORE_ES1, VERSAL_AI_CORE_ES2, VERSAL_AI_EDGE, VERSAL_AI_EDGE_ES1, VERSAL_AI_EDGE_ES2, VERSAL_AI_RF, VERSAL_AI_RF_ES1, VERSAL_AI_RF_ES2, VERSAL_HBM, VERSAL_HBM_ES1, VERSAL_HBM_ES2, VERSAL_PREMIUM, VERSAL_PREMIUM_ES1, VERSAL_PREMIUM_ES2, VERSAL_PRIME, VERSAL_PRIME_ES1 or VERSAL_PRIME_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE);
         #1 $finish;
    end
    end

  generate
       case (SIM_DEVICE)
         "7SERIES" : begin
                        assign out_val = 1'b1;
                        assign out_b_val = 1'b1;
                     end
         "ULTRASCALE" : begin
                        assign out_val = 1'b0;
                        assign out_b_val = 1'bx;
                     end
         default : begin
	 		assign out_val = 1'b0;
	 		assign out_b_val = 1'b0;
	             end
        endcase
   endgenerate

    always @(IO or IOB or DQS_BIAS_BINARY) begin
        if (IO == 1'b1 && IOB == 1'b0) begin
            O_int  <= IO;
            OB_int <= ~IO;
        end
        else if (IO == 1'b0 && IOB == 1'b1) begin
            O_int  <= IO;
            OB_int <= ~IO;
        end
        else if ((IO === 1'bz || IO == 1'b0) && (IOB === 1'bz || IOB == 1'b1)) begin
          if (DQS_BIAS_BINARY == 1'b1) begin
            O_int <= 1'b0;
            OB_int <= 1'b1;
          end else begin
            O_int <= 1'bx;
            OB_int <= 1'bx;
	  end
        end
        else begin
            O_int  <= 1'bx;
            OB_int <= 1'bx;
        end
    end

    generate
       case (USE_IBUFDISABLE)
          "TRUE" :  begin
                       assign T_OR_IBUFDISABLE_1 = ~TM || IBUFDISABLE;
                       assign T_OR_IBUFDISABLE_2 = ~TS || IBUFDISABLE;
                       assign O = (T_OR_IBUFDISABLE_1 == 1'b1) ? out_val : (T_OR_IBUFDISABLE_1 == 1'b0) ? O_int : 1'bx;
                       assign OB = (T_OR_IBUFDISABLE_2 == 1'b1) ? out_b_val : (T_OR_IBUFDISABLE_2 == 1'b0) ? OB_int : 1'bx;
                    end
          "FALSE" : begin
                        assign O = O_int;
                        assign OB = OB_int;
                    end
       endcase
    endgenerate

`ifdef XIL_TIMING
    specify
        (DCITERMDISABLE => O)   = (0:0:0,  0:0:0);
        (DCITERMDISABLE => OB)  = (0:0:0,  0:0:0);
        (DCITERMDISABLE => IO)  = (0:0:0,  0:0:0);
        (DCITERMDISABLE => IOB) = (0:0:0,  0:0:0);
        (I => O)                = (0:0:0,  0:0:0);
        (I => OB)               = (0:0:0,  0:0:0);
        (I => IO)               = (0:0:0,  0:0:0);
        (I => IOB)              = (0:0:0,  0:0:0);
        (IO => O)               = (0:0:0,  0:0:0);
        (IO => OB)              = (0:0:0,  0:0:0);
        (IO => IOB)             = (0:0:0,  0:0:0);
        (IOB => O)              = (0:0:0,  0:0:0);
        (IOB => OB)             = (0:0:0,  0:0:0);
        (IOB => IO)             = (0:0:0,  0:0:0);
        (IBUFDISABLE => O)      = (0:0:0,  0:0:0);
        (IBUFDISABLE => OB)     = (0:0:0,  0:0:0);
        (IBUFDISABLE => IO)     = (0:0:0,  0:0:0);
        (IBUFDISABLE => IOB)    = (0:0:0,  0:0:0);
        (TM => O)               = (0:0:0,  0:0:0);
        (TM => OB)              = (0:0:0,  0:0:0);
        (TM => IO)              = (0:0:0,  0:0:0);
        (TM => IOB)             = (0:0:0,  0:0:0);
        (TS => O)               = (0:0:0,  0:0:0);
        (TS => OB)              = (0:0:0,  0:0:0);
        (TS => IO)              = (0:0:0,  0:0:0);
        (TS => IOB)             = (0:0:0,  0:0:0);
        specparam PATHPULSE$ = 0;
    endspecify
`endif // `ifdef XIL_TIMING
    
endmodule

`endcelldefine
