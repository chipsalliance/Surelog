//
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//


`define ADD 3'b000
`define SUB 3'b001
`define MUL 3'b010
`define LS  3'b011
`define RS  3'b100

module alu(y, a, b, sel, clk, rst_n, en);
input [3:0] a,b;
input [2:0] sel;
input clk, rst_n, en;
output [6:0] y;
reg [6:0] y, y_temp;

always @(a or b or sel)
begin
  if (en)
    begin
      case (sel)
        `ADD : y_temp = a + b;
        `SUB : y_temp = a - b;
        `MUL : y_temp = a * b;
        `LS  : y_temp = a << 1;
        `RS  : y_temp = a >> 1;
       default : y_temp = 0;
      endcase 
`ifdef ALU_BUG1
      // Corrupt response 50% of the time.
      y_temp += ($random % 2);
`endif
    end
  else
     y_temp = 0;

end

always @(posedge clk or negedge rst_n)
  if (!rst_n)
     y <= 0;
  else 
     y = y_temp;


endmodule
