///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2018 Xilinx, Inc.
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
// \   \   \/     Version : 2018.1
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                        Two input AND gate implemented in place of a CLB Latch
// /___/   /\     Filename : AND2B1L.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//    04/01/08 - Initial version.
//    04/14/09 - 517897 - Invert SRI not DI
//    12/13/11 - 524859 - Added `celldefine and `endcelldefine
//    04/16/13 - 683925 - add invertible pin support.
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale  1 ps / 1 ps

`celldefine

module AND2B1L #(
  


  parameter [0:0] IS_SRI_INVERTED = 1'b0
)(
  output O,
  
  input DI,
  input SRI
);
  
// define constants
  localparam MODULE_NAME = "AND2B1L";
  
  reg trig_attr;
// include dynamic registers - XILINX test only



  reg [0:0] IS_SRI_INVERTED_REG = IS_SRI_INVERTED;





  tri0 glblGSR = glbl.GSR;


  wire DI_in;
  wire SRI_in;

  assign DI_in = DI;
  assign SRI_in = SRI ^ IS_SRI_INVERTED_REG;





// begin behavioral model

    assign O = ~glblGSR && DI_in && ~SRI_in;

// end behavioral model












endmodule

`endcelldefine
