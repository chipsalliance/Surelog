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
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                  3-State Diffential Signaling I/O Buffer
// /___/   /\     Filename : IOBUFDS_INTERMDISABLE.v
// \   \  /  \
//  \___\/\___\
//
// Revision:
//    04/20/11 - Initial version.
//    06/15/11 - CR 613347 -- made ouput logic_1 when IBUFDISABLE is active
//    08/31/11 - CR 623170 -- Tristate powergating support
//    09/20/11 - CR 624774, 625725 -- Removed attributes IBUF_DELAY_VALUE, IFD_DELAY_VALUE and CAPACITANCE
//    09/20/11 - CR 625564 -- Fixed Tristate powergating polarity
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//    07/13/12 - 669215 - add parameter DQS_BIAS
//    08/29/12 - 675511 - add DQS_BIAS functionality
//    09/11/12 - 677753 - remove X glitch on O
//    10/22/14 - Added #1 to $finish (CR 808642).
// End Revision

`timescale 1 ps / 1 ps

`celldefine

module IOBUFDS_INTERMDISABLE (O, IO, IOB, I, IBUFDISABLE, INTERMDISABLE, T);

`ifdef XIL_TIMING
    parameter LOC = "UNPLACED";
`endif // `ifdef XIL_TIMING
    parameter DIFF_TERM = "FALSE";
    parameter DQS_BIAS = "FALSE";
    parameter IBUF_LOW_PWR = "TRUE";
    parameter IOSTANDARD = "DEFAULT";
    parameter SIM_DEVICE = "7SERIES";
    parameter SLEW = "SLOW";
    parameter USE_IBUFDISABLE = "TRUE";

  localparam MODULE_NAME = "IOBUFDS_INTERMDISABLE";


    output O;
    inout  IO;
    inout  IOB;
    input  I;
    input  IBUFDISABLE;
    input  INTERMDISABLE;
    input  T;

    wire i_in, io_in, iob_in, ibufdisable_in, intermdisable_in, t_in;
    reg o_out, io_out, iob_out;
    reg O_int;
    wire out_val;

    reg DQS_BIAS_BINARY = 1'b0;
    reg USE_IBUFDISABLE_BINARY = 1'b0;

    wire t_or_gts;
    wire not_t_or_ibufdisable;
//    wire disable_out;

    tri0 GTS = glbl.GTS;

    assign O  =  (USE_IBUFDISABLE_BINARY == 1'b0) ? o_out :
                 ((not_t_or_ibufdisable === 1'b1) ? out_val : ((not_t_or_ibufdisable === 1'b0) ? o_out : 1'bx));

    assign intermdisable_in = INTERMDISABLE;
    assign i_in = I;
    assign ibufdisable_in = IBUFDISABLE;
    assign t_in = T;
    assign io_in = IO;
    assign iob_in = IOB;

    assign t_or_gts = GTS || t_in;
    assign IO  = t_or_gts ? 1'bz :  i_in;
    assign IOB = t_or_gts ? 1'bz : ~i_in;

//    assign disable_out = intermdisable_in && ibufdisable_in;
    assign not_t_or_ibufdisable = ~t_in || ibufdisable_in;


    initial begin

        case (DQS_BIAS)

            "TRUE"  : DQS_BIAS_BINARY <= #1 1'b1;
            "FALSE" : DQS_BIAS_BINARY <= #1 1'b0;
            default : begin
                          $display("Attribute Syntax Error : The attribute DQS_BIAS on %s instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.", MODULE_NAME, DQS_BIAS);
                          #1 $finish;
                      end

        endcase

	case (DIFF_TERM)

            "TRUE", "FALSE" : ;
            default : begin
                          $display("Attribute Syntax Error : The attribute DIFF_TERM on %s instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.", MODULE_NAME, DIFF_TERM);
                          #1 $finish;
                      end

	endcase // case(DIFF_TERM)

        case (IBUF_LOW_PWR)

            "FALSE", "TRUE" : ;
            default : begin
                          $display("Attribute Syntax Error : The attribute IBUF_LOW_PWR on %s instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.", MODULE_NAME, IBUF_LOW_PWR);
                          #1 $finish;
                      end

        endcase

      if((IOSTANDARD == "LVDS_25") || (IOSTANDARD == "LVDSEXT_25")) begin
            $display("DRC Warning : The IOSTANDARD attribute on IOBUFDS_DCIEN instance %m is set to %s.  LVDS_25 is a fixed impedance structure optimized to 100ohm differential. If the intended usage is a bus architecture, please use BLVDS. This is only intended to be used in point to point transmissions that do not have turn around timing requirements", IOSTANDARD);
        end

        case (USE_IBUFDISABLE)

            "TRUE"  : USE_IBUFDISABLE_BINARY <= #1 1'b1;
            "FALSE" : USE_IBUFDISABLE_BINARY <= #1 1'b0;
            default : begin
                          $display("Attribute Syntax Error : The attribute USE_IBUFDISABLE on %s instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.", MODULE_NAME, USE_IBUFDISABLE);
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
                     end
         default : begin
                        assign out_val = 1'b0;
                     end
        endcase
   endgenerate

    always @(io_in or iob_in or DQS_BIAS_BINARY) begin
        if (io_in == 1'b1 && iob_in == 1'b0)
          o_out <= 1'b1;
        else if (io_in == 1'b0 && iob_in == 1'b1)
          o_out <= 1'b0;
        else if ((io_in === 1'bz || io_in == 1'b0) && (iob_in === 1'bz || iob_in == 1'b1))
          if (DQS_BIAS_BINARY == 1'b1)
            o_out <= 1'b0;
          else
            o_out <= 1'bx;
        else if (io_in === 1'bx || iob_in === 1'bx)
          o_out <= 1'bx;
        end


`ifdef XIL_TIMING
    specify
        (I => IO)               = (0:0:0,  0:0:0);
        (I => IOB)              = (0:0:0,  0:0:0);
        (IO => O)               = (0:0:0,  0:0:0);
        (IO => IOB)             = (0:0:0,  0:0:0);
        (IOB => O)              = (0:0:0,  0:0:0);
        (IOB => IO)             = (0:0:0,  0:0:0);
        (IBUFDISABLE => O)      = (0:0:0,  0:0:0);
        (IBUFDISABLE => IO)     = (0:0:0,  0:0:0);
        (IBUFDISABLE => IOB)    = (0:0:0,  0:0:0);
        (INTERMDISABLE => O)   = (0:0:0,  0:0:0);
        (INTERMDISABLE => IO)  = (0:0:0,  0:0:0);
        (INTERMDISABLE => IOB) = (0:0:0,  0:0:0);
        (I => O)                = (0:0:0,  0:0:0);
        (T => O)                = (0:0:0,  0:0:0);
        (T => IO)               = (0:0:0,  0:0:0);
        (T => IOB)              = (0:0:0,  0:0:0);
        specparam PATHPULSE$ = 0;
    endspecify
`endif // `ifdef XIL_TIMING

endmodule

`endcelldefine
