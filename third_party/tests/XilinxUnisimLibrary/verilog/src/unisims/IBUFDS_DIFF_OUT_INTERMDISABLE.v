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
//  \   \         Description : Xilinx Functional Simulation Library Component
//  /   /                  Differential Signaling Input Buffer with Differential Outputs
// /___/   /\     Filename : IBUFDS_DIFF_OUT_INTERMDISABLE.v
// \   \  /  \    Timestamp : Wed Apr 20 17:49:56 PDT 2011
//  \___\/\___\
//
// Revision:
//    04/20/11 - Initial version.
//    06/15/11 - CR 613347 -- made ouput logic_1 when IBUFDISABLE is active
//    08/31/11 - CR 623170 -- added attribute USE_IBUFDISABLE
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//    10/22/14 - Added #1 to $finish (CR 808642).
// End Revision

`timescale  1 ps / 1 ps


`celldefine

module IBUFDS_DIFF_OUT_INTERMDISABLE (O, OB, I, IB, IBUFDISABLE, INTERMDISABLE);

    parameter DIFF_TERM = "FALSE";
    parameter DQS_BIAS = "FALSE";
    parameter IBUF_LOW_PWR = "TRUE";
    parameter IOSTANDARD = "DEFAULT";
    parameter SIM_DEVICE = "7SERIES";
    parameter USE_IBUFDISABLE = "TRUE";
`ifdef XIL_TIMING
    parameter LOC = "UNPLACED";
`endif //  `ifdef XIL_TIMING


    output O; 
    output OB;

    input I;
    input IB;
    input IBUFDISABLE;
    input INTERMDISABLE;

    localparam MODULE_NAME = "IBUFDS_DIFF_OUT_INTERMDISABLE";

    reg  o_out;
    reg DQS_BIAS_BINARY = 1'b0;
    wire out_val;
    wire out_b_val;


    initial begin
         case (DQS_BIAS)

            "TRUE"  : DQS_BIAS_BINARY <= #1 1'b1;
            "FALSE" : DQS_BIAS_BINARY <= #1 1'b0;
            default : begin
                          $display("Attribute Syntax Error : The attribute DQS_BIAS on IBUFDS_DIFF_OUT_INTERMDISABLE instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.", DQS_BIAS);
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

	
        case (DIFF_TERM)

            "TRUE", "FALSE" : ;
            default : begin
                          $display("Attribute Syntax Error : The attribute DIFF_TERM on IBUFDS_DIFF_OUT_INTERMDISABLE instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.", DIFF_TERM);
                          #1 $finish;
                      end

        endcase // case(DIFF_TERM)

        case (IBUF_LOW_PWR)

            "FALSE", "TRUE" : ;
            default : begin
                          $display("Attribute Syntax Error : The attribute IBUF_LOW_PWR on IBUFDS_DIFF_OUT_INTERMDISABLE instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.", IBUF_LOW_PWR);
                          #1 $finish;
                      end

        endcase

    end


    always @(I or IB or DQS_BIAS_BINARY) begin
	if (I == 1'b1 && IB == 1'b0)
	    o_out <= I;
	else if (I == 1'b0 && IB == 1'b1)
	    o_out <= I;
	else if ((I === 1'bz || I == 1'b0) && (IB === 1'bz || IB == 1'b1))
	  if (DQS_BIAS_BINARY == 1'b1)
            o_out <= 1'b0;
          else
            o_out <= 1'bx;
        else if (I == 1'bx || IB == 1'bx)
            o_out <= 1'bx;
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

    generate
       case (USE_IBUFDISABLE)
          "TRUE" :  begin
                       assign O  = (IBUFDISABLE == 0)? o_out  : (IBUFDISABLE == 1)? out_val  : 1'bx;
                       assign OB = (IBUFDISABLE == 0)? ~o_out : (IBUFDISABLE == 1)? out_b_val  : 1'bx;
                    end
          "FALSE" : begin
                       assign O  =  o_out;
                       assign OB =  ~o_out;
                    end
       endcase
    endgenerate

`ifdef XIL_TIMING
    specify
        (I => O)                = (0:0:0,  0:0:0);
        (I => OB)               = (0:0:0,  0:0:0);
        (IB => O)               = (0:0:0,  0:0:0);
        (IB => OB)              = (0:0:0,  0:0:0);
        (IBUFDISABLE => O)      = (0:0:0,  0:0:0);
        (IBUFDISABLE => OB)     = (0:0:0,  0:0:0);
        (INTERMDISABLE => O)    = (0:0:0,  0:0:0);
        (INTERMDISABLE => OB)   = (0:0:0,  0:0:0);
        specparam PATHPULSE$ = 0;
    endspecify
`endif // `ifdef XIL_TIMING

endmodule

`endcelldefine
