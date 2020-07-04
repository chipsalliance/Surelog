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
//  /   /                  D Flip-Flop with Clock Enable and Asynchronous Preset
// /___/   /\     Filename : FDPE.v
// \   \  /  \
//  \___\/\___\
//
// Revision:
//    08/25/10 - Initial version.
//    10/20/10 - remove unused pin line from table.
//    11/01/11 - Disable timing check when set reset active (CR632017)
//    12/08/11 - add MSGON and XON attributes (CR636891)
//    01/16/12 - 640813 - add MSGON and XON functionality
//    04/16/13 - PR683925 - add invertible pin support.
// End Revision

`timescale  1 ps / 1 ps

`celldefine 

module FDPE #(
  




  parameter [0:0] INIT = 1'b1,
  parameter [0:0] IS_C_INVERTED = 1'b0,
  parameter [0:0] IS_D_INVERTED = 1'b0,
  parameter [0:0] IS_PRE_INVERTED = 1'b0
)(
  output Q,
  
  input C,
  input CE,
  input D,
  input PRE
);

    reg [0:0] IS_C_INVERTED_REG = IS_C_INVERTED;
    reg [0:0] IS_D_INVERTED_REG = IS_D_INVERTED;
    reg [0:0] IS_PRE_INVERTED_REG = IS_PRE_INVERTED;
    
    tri0 glblGSR = glbl.GSR;






    wire PRE_in;




    assign PRE_in = (PRE ^ IS_PRE_INVERTED_REG) && (PRE !== 1'bz);


// begin behavioral model

  reg Q_out;

  assign #100 Q = Q_out;

    always @(glblGSR or PRE_in)
      if (glblGSR) 
        assign Q_out = INIT;
      else if (PRE_in === 1'b1) 
        assign Q_out = 1'b1;
      else if (PRE_in === 1'bx) 
        assign Q_out = 1'bx;
      else
        deassign Q_out;


















generate
if (IS_C_INVERTED == 1'b0) begin : generate_block1
  always @(posedge C or posedge PRE_in)
    if (PRE_in || (PRE === 1'bx && Q_out == 1'b1))
      Q_out <= 1'b1;
    else if (CE || (CE === 1'bz) || ((CE === 1'bx) && (Q_out == (D ^ IS_D_INVERTED_REG))))
      Q_out <= D ^ IS_D_INVERTED_REG;
end else begin : generate_block1
  always @(negedge C or posedge PRE_in)
    if (PRE_in || (PRE === 1'bx && Q_out == 1'b1))
      Q_out <= 1'b1;
    else if (CE || (CE === 1'bz) || ((CE === 1'bx) && (Q_out == (D ^ IS_D_INVERTED_REG))))
      Q_out <= D ^ IS_D_INVERTED_REG;
end
endgenerate



































// end behavioral model




























endmodule

`endcelldefine
