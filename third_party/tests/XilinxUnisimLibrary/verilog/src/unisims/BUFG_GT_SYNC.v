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
// /___/  \  /     Vendor      : Xilinx
// \   \   \/      Version     : 2019.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        Synchronizer for BUFG_GT Control Signals
// /___/   /\      Filename    : BUFG_GT_SYNC.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//    02/03/14 - Initial version.
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module BUFG_GT_SYNC
`ifdef XIL_TIMING
#(
  parameter LOC = "UNPLACED"
)
`endif
(
  output CESYNC,
  output CLRSYNC,

  input CE,
  input CLK,
  input CLR
);
  
// define constants
  localparam MODULE_NAME = "BUFG_GT_SYNC";
  
  wire CE_in;
  wire CLK_in;
  wire CLR_in;

  assign CE_in = (CE === 1'bz) || CE; // rv 1
  assign CLK_in = CLK;
  assign CLR_in = (CLR !== 1'bz) && CLR; // rv 0

// begin behavioral model

  assign CESYNC = CE_in;
  assign CLRSYNC = CLR_in;

// end behavioral model

endmodule

`endcelldefine
