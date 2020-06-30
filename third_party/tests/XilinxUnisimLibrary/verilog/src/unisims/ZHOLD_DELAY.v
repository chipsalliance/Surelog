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
//  \   \         Description : Xilinx TEST ONLY Library Component
//  /   /                  Delay Element.
// /___/   /\     Filename : ZHOLD_DELAY.v
// \   \  /  \    
//  \___\/\___\
//
// Revision:
//    04/14/10 - Initial version.
//    05/12/11 - 609212 -- fix for ncsim
//    07/11/11 - 616630 -- Change/Combine attributes
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//    05/10/12 - 659430 - remove GSR ref, ANSI ports, mti simprim error (add #1)
//    10/22/14 - Added #1 to $finish (CR 808642).
// End Revision

`timescale  1 ps / 1 ps
    
`celldefine

module ZHOLD_DELAY #(
`ifdef XIL_TIMING
   parameter LOC = "UNPLACED",
`endif // ifdef XIL_TIMING
   parameter [0:0] IS_DLYIN_INVERTED = 1'b0,
   parameter ZHOLD_FABRIC = "DEFAULT", // {"DEFAULT", "0", .... "31"}
   parameter ZHOLD_IFF = "DEFAULT"  // {"DEFAULT", "0", .... "31"}
) (
   output    DLYFABRIC,
   output    DLYIFF,
   input     DLYIN
);

   localparam MODULE_NAME = "ZHOLD_DELAY";

//------------------- constants ------------------------------------
       localparam MAX_IFF_DELAY_COUNT = 31;
       localparam MIN_IFF_DELAY_COUNT = 0;

       localparam MAX_IDELAY_COUNT = 31;
       localparam MIN_IDELAY_COUNT = 0;

`ifndef XIL_TIMING
       real TAP_DELAY = 200.0;
`endif // ifndef XIL_TIMING

       integer idelay_count=0;
       integer iff_idelay_count=0;

       // inputs
       wire dlyin_in;

`ifndef XIL_TIMING
       // outputs
       reg tap_out_fabric = 0;
       reg tap_out_iff = 0;
`endif // ifndef XIL_TIMING

//----------------------------------------------------------------------
//-------------------------------  Output ------------------------------
//----------------------------------------------------------------------
`ifdef XIL_TIMING
       assign #1 DLYFABRIC = dlyin_in;
       assign #1 DLYIFF    = dlyin_in;
`else  // ifdef XIL_TIMING
       assign DLYFABRIC = tap_out_fabric;
       assign DLYIFF = tap_out_iff;
`endif // ifdef XIL_TIMING

//----------------------------------------------------------------------
//-------------------------------  Input -------------------------------
//----------------------------------------------------------------------
       assign dlyin_in = IS_DLYIN_INVERTED ^ DLYIN;


//------------------------------------------------------------
//---------------------   Initialization  --------------------
//------------------------------------------------------------
       initial begin

        //-------- ZHOLD_FABRIC check
           case (ZHOLD_FABRIC)
               "DEFAULT" : idelay_count = 0;
               "0"       : idelay_count = 0;
               "1"       : idelay_count = 1;
               "2"       : idelay_count = 2;
               "3"       : idelay_count = 3;
               "4"       : idelay_count = 4;
               "5"       : idelay_count = 5;
               "6"       : idelay_count = 6;
               "7"       : idelay_count = 7;
               "8"       : idelay_count = 8;
               "9"       : idelay_count = 9;
               "10"      : idelay_count = 10;
               "11"      : idelay_count = 11;
               "12"      : idelay_count = 12;
               "13"      : idelay_count = 13;
               "14"      : idelay_count = 14;
               "15"      : idelay_count = 15;
               "16"      : idelay_count = 16;
               "17"      : idelay_count = 17;
               "18"      : idelay_count = 18;
               "19"      : idelay_count = 19;
               "20"      : idelay_count = 20;
               "21"      : idelay_count = 21;
               "22"      : idelay_count = 22;
               "23"      : idelay_count = 23;
               "24"      : idelay_count = 24;
               "25"      : idelay_count = 25;
               "26"      : idelay_count = 26;
               "27"      : idelay_count = 27;
               "28"      : idelay_count = 28;
               "29"      : idelay_count = 29;
               "30"      : idelay_count = 30;
               "31"      : idelay_count = 31;
               default : begin
                  $display("Attribute Syntax Error : The attribute ZHOLD_FABRIC on %s instance %m is set to %s.  Legal values for this attribute are \"DEFAULT\", \"0\", \"1\" ..... \"31\"",MODULE_NAME,ZHOLD_FABRIC);
                  #1 $finish;
               end
           endcase

        //-------- ZHOLD_IFF check
           case (ZHOLD_IFF)
               "DEFAULT" : iff_idelay_count = 0;
               "0"       : iff_idelay_count = 0;
               "1"       : iff_idelay_count = 1;
               "2"       : iff_idelay_count = 2;
               "3"       : iff_idelay_count = 3;
               "4"       : iff_idelay_count = 4;
               "5"       : iff_idelay_count = 5;
               "6"       : iff_idelay_count = 6;
               "7"       : iff_idelay_count = 7;
               "8"       : iff_idelay_count = 8;
               "9"       : iff_idelay_count = 9;
               "10"      : iff_idelay_count = 10;
               "11"      : iff_idelay_count = 11;
               "12"      : iff_idelay_count = 12;
               "13"      : iff_idelay_count = 13;
               "14"      : iff_idelay_count = 14;
               "15"      : iff_idelay_count = 15;
               "16"      : iff_idelay_count = 16;
               "17"      : iff_idelay_count = 17;
               "18"      : iff_idelay_count = 18;
               "19"      : iff_idelay_count = 19;
               "20"      : iff_idelay_count = 20;
               "21"      : iff_idelay_count = 21;
               "22"      : iff_idelay_count = 22;
               "23"      : iff_idelay_count = 23;
               "24"      : iff_idelay_count = 24;
               "25"      : iff_idelay_count = 25;
               "26"      : iff_idelay_count = 26;
               "27"      : iff_idelay_count = 27;
               "28"      : iff_idelay_count = 28;
               "29"      : iff_idelay_count = 29;
               "30"      : iff_idelay_count = 30;
               "31"      : iff_idelay_count = 31;
               default : begin
                  $display("Attribute Syntax Error : The attribute ZHOLD_IFF on %s instance %m is set to %s.  Legal values for this attribute are \"DEFAULT\", \"0\", \"1\"...\"31\"",MODULE_NAME,ZHOLD_IFF);
                  #1 $finish;
               end
           endcase

       end // initial begin

`ifndef XIL_TIMING
    always@(dlyin_in) begin
        tap_out_fabric <= #(TAP_DELAY*idelay_count) dlyin_in;
        tap_out_iff    <= #(TAP_DELAY*iff_idelay_count) dlyin_in;
    end  // end always
`endif // ifndef XIL_TIMING

`ifdef XIL_TIMING
    specify
       ( DLYIN => DLYFABRIC) = (0:0:0, 0:0:0);
       ( DLYIN => DLYIFF)    = (0:0:0, 0:0:0);
       specparam PATHPULSE$ = 0;
    endspecify
`endif // ifdef XIL_TIMING

endmodule // ZHOLD_DELAY

`endcelldefine
