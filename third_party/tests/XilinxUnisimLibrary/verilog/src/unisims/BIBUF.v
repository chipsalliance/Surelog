///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2017 Xilinx, Inc.
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
// \   \   \/      Version     : 2018.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                  Bi-Directional IO
// /___/   /\      Filename    : BIBUF.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision:
//
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale  1 ps / 1 ps

`celldefine

module BIBUF
`ifdef XIL_TIMING
#(
  parameter LOC = "UNPLACED"
)
`endif
(
  inout IO,
  inout PAD
);

// define constants
  localparam MODULE_NAME = "BIBUF";

  tri0 glblGSR = glbl.GSR;

// begin behavioral model

    wire PAD_io;
    wire IO_io;

    assign #10 PAD_io = PAD;
    assign #10 IO_io = IO;

    assign (weak1, weak0) IO = PAD_io;
    assign (weak1, weak0) PAD = IO_io;

// end behavioral model

endmodule

`endcelldefine
