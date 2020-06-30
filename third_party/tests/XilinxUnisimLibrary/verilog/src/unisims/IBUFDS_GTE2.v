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
// \   \   \/     Version : 13.1 
//  \   \         Description : Xilinx Timing Simulation Library Component
//  /   /                  Differential Signaling Input Buffer
// /___/   /\     Filename : IBUFDS_GTE2.v
// \   \  /  \    Timestamp : Tue Jun  1 14:31:01 PDT 2010
//  \___\/\___\
//
// Revision:
//    06/01/10 - Initial version.
//    09/29/11 - 627247 -- Changed CLKSWING_CFG from blooean to bits
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//    10/22/14 - Added #1 to $finish (CR 808642).
// End Revision

`timescale 1 ps/1 ps

`celldefine

module IBUFDS_GTE2 (
    O,
    ODIV2,

    CEB,
    I,
    IB
    );
`ifdef XIL_TIMING
    parameter LOC = "UNPLACED";
`endif
    parameter CLKCM_CFG = "TRUE";
    parameter CLKRCV_TRST = "TRUE";
    parameter [1:0] CLKSWING_CFG = 2'b11;

    output O;
    output ODIV2;

    input CEB;
    input I;
    input IB;


// Output signals
    reg  O_out=0, ODIV2_out=0;

// Counters and Flags
    reg [2:0] ce_count = 1;
    reg [2:0] edge_count = 0;

    reg allEqual;

// Attribute settings

// Other signals
    reg clkcm_cfg_int = 0;
    reg clkrcv_trst_int = 0;
    reg clkswing_cfg_int = 0;

    reg [1:0] CLKSWING_CFG_BINARY;
    reg notifier;

    initial begin
        allEqual = 0;

//-------------------------------------------------
//----- CLKCM_CFG check
//-------------------------------------------------
        case (CLKCM_CFG)

            "FALSE" : clkcm_cfg_int <= 1'b0;
            "TRUE"  : clkcm_cfg_int <= 1'b1;
            default : begin
                          $display("Attribute Syntax Error : The attribute CLKCM_CFG on IBUFDS_GTE2 instance %m is set to %s.  Legal values for this attribute are FALSE or TRUE", CLKCM_CFG);
                          #1 $finish;
                      end

        endcase // case(CLKCM_CFG)

//-------------------------------------------------
//----- CLKRCV_TRST check
//-------------------------------------------------
        case (CLKRCV_TRST)

            "FALSE" : clkrcv_trst_int <= 1'b0;
            "TRUE"  : clkrcv_trst_int <= 1'b1;
            default : begin
                          $display("Attribute Syntax Error : The attribute CLKRCV_TRST on IBUFDS_GTE2 instance %m is set to %s.  Legal values for this attribute are FALSE or TRUE", CLKRCV_TRST);
                          #1 $finish;
                      end

        endcase // case(CLKRCV_TRST)

    end  // initial begin


// =====================
// Count the rising edges of the clk
// =====================
    always @(posedge I) begin
         if(allEqual)
             edge_count <= 3'b000;
          else
             if (CEB == 1'b0)
                 edge_count <= edge_count + 1;
     end

//  Generate synchronous reset after DIVIDE number of counts
    always @(edge_count)
        if (edge_count == ce_count)
           allEqual = 1;
        else
          allEqual = 0;

// =====================
// Generate ODIV2
// =====================
    always @(posedge I)
        ODIV2_out <= allEqual;

// =====================
// Generate O
// =====================
    always @(I)
        O_out <= I & ~CEB;


// =====================
// Outputs   
// =====================

    assign O  = O_out;
    assign ODIV2   = ODIV2_out;
    

    specify
`ifdef XIL_TIMING
       $period (posedge I, 0:0:0, notifier);
       $period (posedge IB, 0:0:0, notifier);
       ( I => O) = (100:100:100, 100:100:100);
       ( I => ODIV2) = (100:100:100, 100:100:100);
       ( IB => O) = (100:100:100, 100:100:100);
       ( IB => ODIV2) = (100:100:100, 100:100:100);
`endif
       specparam PATHPULSE$ = 0;

    endspecify

endmodule

`endcelldefine
