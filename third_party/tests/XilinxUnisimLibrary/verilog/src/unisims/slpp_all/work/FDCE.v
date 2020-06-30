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
// /___/  \  /    Vendor : Xilinx
// \   \   \/     Version : 2017.1
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                  D Flip-Flop with Clock Enable and Asynchronous Clear
// /___/   /\     Filename : FDCE.v
// \   \  /  \
//  \___\/\___\
//
// Revision:
//    08/24/10 - Initial version.
//    10/20/10 - remove unused pin line from table.
//    11/01/11 - Disable timing check when set reset active (CR632017)
//    12/08/11 - add MSGON and XON attributes (CR636891)
//    01/16/12 - 640813 - add MSGON and XON functionality
//    04/16/13 - PR683925 - add invertible pin support.
// End Revision

`timescale  1 ps / 1 ps


`celldefine 


module FDCE #(
  




  parameter [0:0] INIT = 1'b0,
  parameter [0:0] IS_CLR_INVERTED = 1'b0,
  parameter [0:0] IS_C_INVERTED = 1'b0,
  parameter [0:0] IS_D_INVERTED = 1'b0
)(
  output Q,
  
  input C,
  input CE,
  input CLR,
  input D
);

    reg [0:0] IS_CLR_INVERTED_REG = IS_CLR_INVERTED;
    reg [0:0] IS_C_INVERTED_REG = IS_C_INVERTED;
    reg [0:0] IS_D_INVERTED_REG = IS_D_INVERTED;
    
    tri0 glblGSR = glbl.GSR;






    wire CLR_in;




    assign CLR_in = (CLR ^ IS_CLR_INVERTED_REG) && (CLR !== 1'bz);


// begin behavioral model

  reg Q_out;

  assign #100 Q = Q_out;

    always @(glblGSR or CLR_in)
      if (glblGSR) 
        assign Q_out = INIT;
      else if (CLR_in === 1'b1) 
        assign Q_out = 1'b0;
      else if (CLR_in === 1'bx) 
        assign Q_out = 1'bx;
      else
        deassign Q_out;


















generate
if (IS_C_INVERTED == 1'b0) begin : generate_block1
  always @(posedge C or posedge CLR_in)
    if (CLR_in || (CLR === 1'bx && Q_out == 1'b0))
      Q_out <= 1'b0;
    else if (CE || (CE === 1'bz) || ((CE === 1'bx) && (Q_out == (D ^ IS_D_INVERTED_REG))))
      Q_out <= D ^ IS_D_INVERTED_REG;
end else begin : generate_block1
  always @(negedge C or posedge CLR_in)
    if (CLR_in || (CLR === 1'bx && Q_out == 1'b0))
      Q_out <= 1'b0;
    else if (CE || (CE === 1'bz) || ((CE === 1'bx) && (Q_out == (D ^ IS_D_INVERTED_REG))))
      Q_out <= D ^ IS_D_INVERTED_REG;
end
endgenerate



































// end behavioral model




























endmodule

`endcelldefine

