///////////////////////////////////////////////////////
//     Copyright (c) 2009 Xilinx Inc.
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
// \  \    \/      Version     :  12.1
//  \  \           Description : 
//  /  /                      
// /__/   /\       Filename    : BUFMRCE.v
// \  \  /  \ 
//  \__\/\__ \                    
//                                 
//  Revision:		1.0
//  05/24/12 - 661573 - Remove 100 ps delay
///////////////////////////////////////////////////////

`timescale 1 ps / 1 ps 

`celldefine

module BUFMRCE #(
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

  wire   NCE, o_bufg_o, o_bufg1_o;
  reg  CE_TYPE_BINARY;
  reg  INIT_OUT_BINARY;
  reg  IS_CE_INVERTED_BIN = IS_CE_INVERTED;

  `ifdef XIL_TIMING //Simprim 
  reg notifier;
  `endif

  wire O_OUT;

  wire delay_CE;
  wire delay_I;

  initial begin
    case (CE_TYPE)
      "SYNC" : CE_TYPE_BINARY = 1'b0;
      "ASYNC" : CE_TYPE_BINARY = 1'b1;
      default : begin
        $display("Attribute Syntax Error : The Attribute CE_TYPE on BUFMRCE instance %m is set to %s.  Legal values for this attribute are SYNC, or ASYNC.", CE_TYPE);
        #1 $finish;
      end
    endcase

    if ((INIT_OUT >= 0) && (INIT_OUT <= 1))
      INIT_OUT_BINARY = INIT_OUT;
    else begin
      $display("Attribute Syntax Error : The Attribute INIT_OUT on BUFMRCE instance %m is set to %d.  Legal values for this attribute are  0 to 1.", INIT_OUT);
      #1 $finish;
    end

  end

    
    BUFGCTRL #(.INIT_OUT(1'b0), .PRESELECT_I0("TRUE"), .PRESELECT_I1("FALSE")) B1 
	(.O(o_bufg_o), .CE0(~NCE), .CE1(NCE), .I0(delay_I), .I1(1'b0), .IGNORE0(1'b0), .IGNORE1(1'b0), .S0(1'b1), .S1(1'b1));

    
    INV I1 (.I(delay_CE ^ IS_CE_INVERTED_BIN), .O(NCE));

    
    BUFGCTRL #(.INIT_OUT(1'b1), .PRESELECT_I0("TRUE"), .PRESELECT_I1("FALSE")) B2
	(.O(o_bufg1_o), .CE0(~NCE), .CE1(NCE), .I0(delay_I), .I1(1'b1), .IGNORE0(1'b0), .IGNORE1(1'b0), .S0(1'b1), .S1(1'b1));

    
    assign O = (INIT_OUT == 1) ? o_bufg1_o : o_bufg_o;

`ifndef XIL_TIMING
    
    assign delay_I = I;
    assign delay_CE = CE;
    
`endif

  specify
    ( I => O) = (0:0:0, 0:0:0);

  `ifdef XIL_TIMING

    $period (posedge I, 0:0:0, notifier);
    $setuphold (negedge I, negedge CE, 0:0:0, 0:0:0, notifier,,, delay_I, delay_CE);
    $setuphold (negedge I, posedge CE, 0:0:0, 0:0:0, notifier,,, delay_I, delay_CE);
    $setuphold (posedge I, negedge CE, 0:0:0, 0:0:0, notifier,,, delay_I, delay_CE);
    $setuphold (posedge I, posedge CE, 0:0:0, 0:0:0, notifier,,, delay_I, delay_CE);

  `endif //  `ifdef XIL_TIMING

    specparam PATHPULSE$ = 0;
  endspecify
endmodule

`endcelldefine
