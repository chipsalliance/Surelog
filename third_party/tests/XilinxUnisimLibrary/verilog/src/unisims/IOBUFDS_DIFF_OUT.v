///////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2004 Xilinx, Inc.
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
// \   \   \/     Version : 12.0
//  \   \         Description : Xilinx Functional and Timing Simulation Library Component
//  /   /                  3-State Diffential Signaling I/O Buffer
// /___/   /\     Filename : IOBUFDS_DIFF_OUT.v
// \   \  /  \    Timestamp : Tue May 26 17:09:31 PDT 2009
//  \___\/\___\
//
// Revision:
//    05/26/09 - Initial version.
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//    10/22/14 - Added #1 to $finish (CR 808642).
// End Revision

`timescale  1 ps / 1 ps


`celldefine

module IOBUFDS_DIFF_OUT (O, OB, IO, IOB, I, TM, TS);

    parameter DIFF_TERM = "FALSE";
    parameter DQS_BIAS = "FALSE";
    parameter IBUF_LOW_PWR = "TRUE";
    parameter IOSTANDARD = "DEFAULT";

`ifdef XIL_TIMING

    parameter LOC = "UNPLACED";

`endif

    
    output O;
    output OB;
    inout  IO;
    inout  IOB;
    input  I;
    input  TM;
    input  TS;

    wire t1, t2;
    reg DQS_BIAS_BINARY = 1'b0;

    tri0 GTS = glbl.GTS;

    reg O_out, OB_out;
    
    or O1 (t1, GTS, TM);
    bufif0 B1 (IO, I, t1);

    or O2 (t2, GTS, TS);
    notif0 N2 (IOB, I, t2);

    assign O = O_out;
    assign OB = OB_out;
    
    initial begin
	
        case (DIFF_TERM)

            "TRUE", "FALSE" : ;
            default : begin
                          $display("Attribute Syntax Error : The attribute DIFF_TERM on IOBUFDS_DIFF_OUT instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.", DIFF_TERM);
                          #1 $finish;
                      end

        endcase // case(DIFF_TERM)

	
	case (IBUF_LOW_PWR)

            "FALSE", "TRUE" : ;
            default : begin
                          $display("Attribute Syntax Error : The attribute IBUF_LOW_PWR on IOBUFDS_DIFF_OUT instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.", IBUF_LOW_PWR);
                          #1 $finish;
                      end

	endcase // case(IBUF_LOW_PWR)

	case (DQS_BIAS)

            "TRUE"  : DQS_BIAS_BINARY <= #1 1'b1;
            "FALSE" : DQS_BIAS_BINARY <= #1 1'b0;
            default : begin
                          $display("Attribute Syntax Error : The attribute DQS_BIAS on IOBUFDS_DIFF_OUT instance %m is set to %s.  Legal values for this attribute are TRUE or FALSE.", DQS_BIAS);
                          #1 $finish;
                      end

        endcase


	
    end


    always @(IO or IOB or DQS_BIAS_BINARY) begin
        if (IO == 1'b1 && IOB == 1'b0) begin
            O_out  <= IO;
            OB_out <= ~IO;
        end
        else if (IO == 1'b0 && IOB == 1'b1) begin
            O_out  <= IO;
            OB_out <= ~IO;
        end
	else if ((IO === 1'bz || IO == 1'b0) && (IOB === 1'bz || IOB == 1'b1)) begin
          if (DQS_BIAS_BINARY == 1'b1) begin
            O_out <= 1'b0;
            OB_out <= 1'b1;
          end else begin
            O_out <= 1'bx;
            OB_out <= 1'bx;
	  end
        end
        else begin
            O_out  <= 1'bx;
            OB_out <= 1'bx;
        end
    end

    
`ifdef XIL_TIMING

    specify
        (I => O) = (0:0:0, 0:0:0);
	(I => OB) = (0:0:0, 0:0:0);
        (I => IO) = (0:0:0, 0:0:0);
        (I => IOB) = (0:0:0, 0:0:0);
        (TM => O) = (0:0:0, 0:0:0);
	(TM => OB) = (0:0:0, 0:0:0);
        (TM => IO) = (0:0:0, 0:0:0);
        (TM => IOB) = (0:0:0, 0:0:0);
	(TS => O) = (0:0:0, 0:0:0);
	(TS => OB) = (0:0:0, 0:0:0);
        (TS => IO) = (0:0:0, 0:0:0);
        (TS => IOB) = (0:0:0, 0:0:0);
        (IO => O) = (0:0:0, 0:0:0);
	(IO => OB) = (0:0:0, 0:0:0);
        (IO => IO) = (0:0:0, 0:0:0);
        (IO => IOB) = (0:0:0, 0:0:0);
        (IOB => O) = (0:0:0, 0:0:0);
	(IOB => OB) = (0:0:0, 0:0:0);
        (IOB => IO) = (0:0:0, 0:0:0);
        (IOB => IOB) = (0:0:0, 0:0:0);
        specparam PATHPULSE$ = 0;
    endspecify

`endif

    
endmodule

`endcelldefine
