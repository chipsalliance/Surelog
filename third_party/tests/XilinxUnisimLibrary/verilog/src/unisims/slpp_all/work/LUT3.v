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
//  /   /                  3-Bit Look-Up Table
// /___/   /\     Filename : LUT3.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//    03/23/04 - Initial version.
//    03/11/05 - Add LOC Parameter
//    12/13/11 - 524859 - Added `celldefine and `endcelldefine
//    09/12/16 - ANSI ports, speed improvements
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps/1 ps

`celldefine

module LUT3 #(



  parameter [7:0] INIT = 8'h00
)(
  output O,

  input I0,
  input I1,
  input I2
);

// define constants
  localparam MODULE_NAME = "LUT3";

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only



  reg [7:0] INIT_REG = INIT;


  x_lut3_mux8 (O, INIT_REG[7], INIT_REG[6], INIT_REG[5], INIT_REG[4], INIT_REG[3], INIT_REG[2], INIT_REG[1], INIT_REG[0], I2, I1, I0);










endmodule

`endcelldefine

primitive x_lut3_mux8 (o, d7, d6, d5, d4, d3, d2, d1, d0, s2, s1, s0);

  output o;
  input d7, d6, d5, d4, d3, d2, d1, d0;
  input s2, s1, s0;

  table

    // d7  d6  d5  d4  d3  d2  d1  d0  s2  s1  s0 : o;

       ?   ?   ?   ?   ?   ?   ?   1000 : 1;
       ?   ?   ?   ?   ?   ?   ?   0000 : 0;
       ?   ?   ?   ?   ?   ?   1 ?   001 : 1;
       ?   ?   ?   ?   ?   ?   0 ?   001 : 0;
       ?   ?   ?   ?   ?   1 ?   ?   010 : 1;
       ?   ?   ?   ?   ?   0 ?   ?   010 : 0;
       ?   ?   ?   ?   1 ?   ?   ?   011 : 1;
       ?   ?   ?   ?   0 ?   ?   ?   011 : 0;
       ?   ?   ?   1 ?   ?   ?   ?   100 : 1;
       ?   ?   ?   0 ?   ?   ?   ?   100 : 0;
       ?   ?   1 ?   ?   ?   ?   ?   101 : 1;
       ?   ?   0 ?   ?   ?   ?   ?   101 : 0;
       ?   1 ?   ?   ?   ?   ?   ?   110 : 1;
       ?   0 ?   ?   ?   ?   ?   ?   110 : 0;
       1 ?   ?   ?   ?   ?   ?   ?   111 : 1;
       0 ?   ?   ?   ?   ?   ?   ?   111 : 0;

       ?   ?   ?   ?   ?   ?   0000 x  : 0;
       ?   ?   ?   ?   ?   ?   1100 x  : 1;
       ?   ?   ?   ?   00 ?   ?   01 x  : 0;
       ?   ?   ?   ?   11 ?   ?   01 x  : 1;
       ?   ?   00 ?   ?   ?   ?   10 x  : 0;
       ?   ?   11 ?   ?   ?   ?   10 x  : 1;
       00 ?   ?   ?   ?   ?   ?   11 x  : 0;
       11 ?   ?   ?   ?   ?   ?   11 x  : 1;

       ?   ?   ?   ?   ?   0 ?   00 x   0 : 0;
       ?   ?   ?   ?   ?   1 ?   10 x   0 : 1;
       ?   ?   ?   ?   0 ?   0 ?   0 x   1 : 0;
       ?   ?   ?   ?   1 ?   1 ?   0 x   1 : 1;
       ?   0 ?   0 ?   ?   ?   ?   1 x   0 : 0;
       ?   1 ?   1 ?   ?   ?   ?   1 x   0 : 1;
       0 ?   0 ?   ?   ?   ?   ?   1 x   1 : 0;
       1 ?   1 ?   ?   ?   ?   ?   1 x   1 : 1;

       ?   ?   ?   0 ?   ?   ?   0 x   00 : 0;
       ?   ?   ?   1 ?   ?   ?   1 x   00 : 1;
       ?   ?   0 ?   ?   ?   0 ?   x   01 : 0;
       ?   ?   1 ?   ?   ?   1 ?   x   01 : 1;
       ?   0 ?   ?   ?   0 ?   ?   x   10 : 0;
       ?   1 ?   ?   ?   1 ?   ?   x   10 : 1;
       0 ?   ?   ?   0 ?   ?   ?   x   11 : 0;
       1 ?   ?   ?   1 ?   ?   ?   x   11 : 1;

       ?   ?   ?   ?   00000 x   x  : 0;
       ?   ?   ?   ?   11110 x   x  : 1;
       0000 ?   ?   ?   ?   1 x   x  : 0;
       1111 ?   ?   ?   ?   1 x   x  : 1;

       ?   ?   00 ?   ?   00 x   0 x  : 0;
       ?   ?   11 ?   ?   11 x   0 x  : 1;
       00 ?   ?   00 ?   ?   x   1 x  : 0;
       11 ?   ?   11 ?   ?   x   1 x  : 1;

       ?   0 ?   0 ?   0 ?   0 x   x   0 : 0;
       ?   1 ?   1 ?   1 ?   1 x   x   0 : 1;
       0 ?   0 ?   0 ?   0 ?   x   x   1 : 0;
       1 ?   1 ?   1 ?   1 ?   x   x   1 : 1;

       00000000 x   x   x  : 0;
       11111111 x   x   x  : 1;

  endtable

endprimitive
