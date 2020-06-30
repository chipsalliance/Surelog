///////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2009 Xilinx, Inc.
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
// \   \   \/     Version : 13.i 
//  \   \         Description : Xilinx Timing Simulation Library Component
//  /   /                       H Clock Buffer with Active High Enable
// /___/   /\     Filename : BUFHCE.v
// \   \  /  \    Timestamp : Wed Apr 22 17:10:55 PDT 2009
//  \___\/\___\
//
// Revision:
//    04/08/08 - Initial version.
//    09/19/08 - Add GSR
//    10/19/08 - Recoding to same as BUFGCE according to hardware.
//    11/15/10 - Add CE_TYPE attribute (CR578114)
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//  05/24/12 - 661573 - Remove 100 ps delay
//    10/12/12 - 681696 - fix preselect behavior.
//    10/30/12 - 684744 - match mapping with ISE.
//    10/22/14 - Added #1 to $finish (CR 808642).
// End Revision

`timescale 1 ps/1 ps

`celldefine

module BUFHCE #(
  `ifdef XIL_TIMING //Simprim 
  parameter LOC = "UNPLACED",
  `endif
  parameter CE_TYPE = "SYNC",
  parameter integer INIT_OUT = 0,
  parameter [0:0] IS_CE_INVERTED = 1'b0
)(
  output O,

  input CE,
  input I
);

  `ifdef XIL_TIMING //Simprim 
  reg notifier;
  `endif
  wire del_I, delCE;
  wire  NCE, o_bufg_o, o_bufg1_o;
  reg CE_TYPE_BINARY;
  reg INIT_OUT_BINARY;
  reg IS_CE_INVERTED_BIN = IS_CE_INVERTED;

  initial begin
    case (CE_TYPE)
      "SYNC" : CE_TYPE_BINARY = 1'b0;
      "ASYNC" : CE_TYPE_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute CE_TYPE on BUFHCE instance %m is set to %s.  Legal values for this attribute are SYNC, or ASYNC.", CE_TYPE);
        #1 $finish;
      end
    endcase

    if ((INIT_OUT >= 0) && (INIT_OUT <= 1))
      INIT_OUT_BINARY = INIT_OUT;
    else begin
      $display("Attribute Syntax Error : The Attribute INIT_OUT on BUFHCE instance %m is set to %d.  Legal values for this attribute are  0 to 1.", INIT_OUT);
      #1 $finish;
    end

  end

    
    BUFGCTRL bufgctrl0_inst (.O(o_bufg_o),
			     .CE0(~NCE),
			     .CE1(NCE),
			     .I0(del_I),
			     .I1(1'b0), 
			     .IGNORE0(CE_TYPE_BINARY), 
			     .IGNORE1(1'b0), 
			     .S0(1'b1), 
			     .S1(1'b1));
    
    defparam bufgctrl0_inst.INIT_OUT = 1'b0;
    defparam bufgctrl0_inst.PRESELECT_I0 = "TRUE";
    defparam bufgctrl0_inst.PRESELECT_I1 = "FALSE";
                               
                                       
    INV I1 (.I(delCE ^ IS_CE_INVERTED_BIN),
            .O(NCE));

    
    BUFGCTRL bufgctrl1_inst (.O(o_bufg1_o), 
			     .CE0(~NCE), 
			     .CE1(NCE), 
			     .I0(del_I), 
			     .I1(1'b1), 
			     .IGNORE0(CE_TYPE_BINARY), 
			     .IGNORE1(1'b0), 
			     .S0(1'b1), 
			     .S1(1'b1));
    
    defparam bufgctrl1_inst.INIT_OUT = 1'b0;
    defparam bufgctrl1_inst.PRESELECT_I0 = "TRUE";
    defparam bufgctrl1_inst.PRESELECT_I1 = "FALSE";

    
    assign O = (INIT_OUT == 1) ? o_bufg1_o : o_bufg_o;

    
`ifndef XIL_TIMING
    
    assign del_I = I;
    assign delCE = CE;
    
`endif

    
    specify

	(I => O) = (0:0:0, 0:0:0);
      
`ifdef XIL_TIMING

	$period (posedge I, 0:0:0, notifier);
	$setuphold (negedge I, negedge CE, 0:0:0, 0:0:0, notifier,,, del_I, delCE);
	$setuphold (negedge I, posedge CE, 0:0:0, 0:0:0, notifier,,, del_I, delCE);
	$setuphold (posedge I, negedge CE, 0:0:0, 0:0:0, notifier,,, del_I, delCE);
	$setuphold (posedge I, posedge CE, 0:0:0, 0:0:0, notifier,,, del_I, delCE);

`endif

	specparam PATHPULSE$ = 0;
	
    endspecify

    
endmodule

`endcelldefine
