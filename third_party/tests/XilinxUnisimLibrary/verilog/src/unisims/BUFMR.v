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
// /__/   /\       Filename    : BUFMR.v
// \  \  /  \ 
//  \__\/\__ \                    
//                                 
//  Revision:		1.0
//  05/24/12 - 661573 - Remove 100 ps delay
///////////////////////////////////////////////////////

`timescale 1 ps / 1 ps 

`celldefine

module BUFMR (
  O,

  I
);

`ifdef XIL_TIMING

    parameter LOC = "UNPLACED";
    reg notifier;

`endif 

  output O;

  input I;


  buf B1 (O, I);

  specify

  ( I => O) = (0:0:0, 0:0:0);

`ifdef XIL_TIMING

  $period (posedge I, 0:0:0, notifier);

`endif 

  specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
