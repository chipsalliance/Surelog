///////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2016 Xilinx, Inc.
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
// /___/  \  /    Vendor      : Xilinx
// \   \   \/     Version     : 2017.1
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                  16-Bit Shift Register Look-Up-Table with Carry and Clock Enable
// /___/   /\     Filename    : SRLC16E.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision
//    03/23/04 - Initial version.
//    03/11/05 - Add LOC paramter;
//    05/07/08 - 468872 - Add negative setup/hold support
//    12/13/11 - 524859 - Added `celldefine and `endcelldefine
//    04/16/13 - 683925 - add invertible pin support.
// End Revision
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps/1 ps


`celldefine


module SRLC16E #(
  


  parameter [15:0] INIT = 16'h0000,
  parameter [0:0] IS_CLK_INVERTED = 1'b0
)(
  output Q,
  output Q15,
  
  input A0,
  input A1,
  input A2,
  input A3,
  input CE,
  input CLK,
  input D
);







  reg  [15:0] data = INIT;
  reg first_time = 1'b1;

  initial
  begin
    assign  data = INIT;
    first_time <= #100000 1'b0;





    while ((((CLK !== 1'b0) && (IS_CLK_INVERTED == 1'b0)) ||
            ((CLK !== 1'b1) && (IS_CLK_INVERTED == 1'b1))) &&
           (first_time == 1'b1)) #1000;

    deassign data;
  end
















generate
if (IS_CLK_INVERTED == 1'b0) begin : generate_block1
  always @(posedge CLK) begin
    if (CE == 1'b1 || CE === 1'bz) begin //rv 1
      data[15:0] <= {data[14:0], D};
    end
  end
end else begin : generate_block1
  always @(negedge CLK) begin
    if (CE == 1'b1 || CE === 1'bz) begin //rv 1
      data[15:0] <= {data[14:0], D};
    end
  end
end
endgenerate


  assign Q = data[{A3, A2, A1, A0}];
  assign Q15 = data[15];



















  specify
    (A0 => Q) = (0:0:0, 0:0:0);
    (A1 => Q) = (0:0:0, 0:0:0);
    (A2 => Q) = (0:0:0, 0:0:0);
    (A3 => Q) = (0:0:0, 0:0:0);
    (CLK => Q) = (100:100:100, 100:100:100);
    (CLK => Q15) = (100:100:100, 100:100:100);














    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine

