///////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2014 Xilinx, Inc.
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
// \   \   \/     Version : 2014.4
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                  Transparent Data Latch with Asynchronous Preset and Gate Enable
// /___/   /\     Filename : LDPE.v
// \   \  /  \
//  \___\/\___\
//
// Revision:
//    08/25/10 - Initial version.
//    11/01/11 - Disable timing check when set reset active (CR633224)
//    12/08/11 - add MSGON and XON attribures (CR636891)
//    01/16/12 - 640813 - add MSGON and XON functionality
//    04/16/13 - PR683925 - add invertible pin support.
// End Revision

`timescale  1 ps / 1 ps

`celldefine
module LDPE #(
  



  parameter [0:0] INIT = 1'b1,
  parameter [0:0] IS_G_INVERTED = 1'b0,
  parameter [0:0] IS_PRE_INVERTED = 1'b0
)(
  output Q,

  input D,
  input G,
  input GE,
  input PRE
);

  wire [0:0] IS_G_INVERTED_BIN;
  wire [0:0] IS_PRE_INVERTED_BIN;

  reg Q_out = INIT;

  wire D_in;
  wire GE_in;
  wire G_in;
  wire PRE_in;

  assign IS_G_INVERTED_BIN = IS_G_INVERTED;
  assign IS_PRE_INVERTED_BIN = IS_PRE_INVERTED;










  assign D_in = D;
  assign G_in = G ^ IS_G_INVERTED_BIN;
  assign GE_in = (GE === 1'bz) || GE; // rv 1
  assign PRE_in = (PRE !== 1'bz) && (PRE ^ IS_PRE_INVERTED_BIN); // rv 0


  assign Q = Q_out;

  reg notifier;
  wire notifier1;
  reg rst_int, set_int;
  wire o_out;











  tri0 GSR = glbl.GSR;
    





















  assign notifier1 = 1'bx;

    
  always @(GSR or PRE_in) begin
    if (GSR) begin
      if (INIT) begin
        rst_int = 1'b0;
        set_int = 1'b1;
      end
      else begin
        rst_int = 1'b1;
        set_int = 1'b0;
      end
    end
    else begin
      rst_int = 1'b0;
      set_int = PRE_in;
    end
  end

  latchsre_ldpe (o_out, G_in, D_in, set_int, rst_int, GE_in, notifier1);
    
  always @(o_out)
      Q_out = o_out;

    
  specify
    (D => Q) = (100:100:100, 100:100:100);
    (G => Q) = (100:100:100, 100:100:100);
    (GE => Q) = (0:0:0, 0:0:0);


























      specparam PATHPULSE$ = 0;
  endspecify

    
endmodule

`endcelldefine


primitive latchsre_ldpe (q, clk, d, set, rst, ge, notifier);

  output q; reg q;
  input clk, d, set, rst, ge, notifier;

  table

    //   clk    d   set   rst   ge  notifier   q     q+;

          10001 ?   :   ?  :  0;
          11001 ?   :   ?  :  1;

          0 ?    00 ?      ?   :   ?  :  -;
          ?     ?    000 ?   :   ?  :  -;
          ?     00 ?    ?      ?   :   0 :  -;
          ?     1 ?     0 ?      ?   :   1 :  -;

          ?     ?    10 ?      ?   :   ?  :  1;
          ?     ?    ?     1 ?      ?   :   ?  :  0;
          0 ?    0 x    ?      ?   :   0 :  0;
          ?     ?    0 x    0 ?   :   0 :  0;
          100 x    1 ?   :   ?  :  0;
          0 ?    x     0 ?      ?   :   1 :  1;
          ?     ?    x     00 ?   :   1 :  1;
          11 x     01 ?   :   ?  :  1;
          ?     ?    ?     ?    ?      *   :   ?  :  x;

  endtable

endprimitive
