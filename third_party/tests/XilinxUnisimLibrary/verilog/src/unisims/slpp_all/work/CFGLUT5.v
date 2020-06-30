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
//  /   /                  5-input Dynamically Reconfigurable Look-Up-Table with Carry and Clock Enable
// /___/   /\     Filename    : CFGLUT5.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision
//    12/27/05 - Initial version.
//    12/13/11 - 524859 - Added `celldefine and `endcelldefine
//    05/13/13 - add IS_CLK_INVERTED
// End Revision
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps/1 ps


`celldefine


module CFGLUT5 #(
  


  parameter [31:0] INIT = 32'h00000000,
  parameter [0:0] IS_CLK_INVERTED = 1'b0
)(
  output CDO,
  output O5,
  output O6,
  
  input CDI,
  input CE,
  input CLK,
  input I0,
  input I1,
  input I2,
  input I3,
  input I4
);







  reg  [31:0] data = INIT;
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
    if (CE == 1'b1) begin
      data[31:0] <= {data[30:0], CDI};
    end
  end
end else begin : generate_block1
  always @(negedge CLK) begin
    if (CE == 1'b1) begin
      data[31:0] <= {data[30:0], CDI};
    end
  end
end
endgenerate


  assign  O6 = data[{I4,I3,I2,I1,I0}];
  assign  O5 = data[{1'b0,I3,I2,I1,I0}];
  assign  CDO = data[31];



















  specify
    (CLK => CDO) = (100:100:100, 100:100:100);
    (CLK => O5) = (100:100:100, 100:100:100);
    (CLK => O6) = (100:100:100, 100:100:100);
    (I0 => CDO) = (0:0:0, 0:0:0);
    (I0 => O5) = (0:0:0, 0:0:0);
    (I0 => O6) = (0:0:0, 0:0:0);
    (I1 => CDO) = (0:0:0, 0:0:0);
    (I1 => O5) = (0:0:0, 0:0:0);
    (I1 => O6) = (0:0:0, 0:0:0);
    (I2 => CDO) = (0:0:0, 0:0:0);
    (I2 => O5) = (0:0:0, 0:0:0);
    (I2 => O6) = (0:0:0, 0:0:0);
    (I3 => CDO) = (0:0:0, 0:0:0);
    (I3 => O5) = (0:0:0, 0:0:0);
    (I3 => O6) = (0:0:0, 0:0:0);
    (I4 => CDO) = (0:0:0, 0:0:0);
    (I4 => O5) = (0:0:0, 0:0:0);
    (I4 => O6) = (0:0:0, 0:0:0);














    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine

