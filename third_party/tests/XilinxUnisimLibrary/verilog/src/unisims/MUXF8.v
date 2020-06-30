///////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2009 Xilinx, Inc.
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
// \   \   \/     Version : 10.1
//  \   \         Description : Xilinx Functional Simulation Library Component
//  /   /                  2-to-1 Lookup Table Multiplexer with General Output
// /___/   /\     Filename : MUXF8.v
// \   \  /  \    Timestamp : Thu Mar 25 16:42:56 PST 2004
//  \___\/\___\
//
// Revision:
//    03/23/04 - Initial version.
//    02/04/05 - Rev 0.0.1 Remove input/output bufs; Remove unnessasary begin/end;
//    05/10/07 - When input same, output same for any sel value. (CR434611).
//    08/23/07 - User block statement (CR446704).
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
// End Revision

`timescale  1 ps / 1 ps


`celldefine

module MUXF8 (O, I0, I1, S);


`ifdef XIL_TIMING

    parameter LOC = "UNPLACED";

`endif

    
    output O;
    input I0, I1, S;
    
    reg O_out;

    always @(I0 or I1 or S) 
        if (S)
	    O_out = I1;
	else
	    O_out = I0;
    
    assign O = O_out;
    
`ifdef XIL_TIMING

    specify
                                                                                 
        (I0 => O) = (0:0:0, 0:0:0);
        (I1 => O) = (0:0:0, 0:0:0);
	(S => O) = (0:0:0, 0:0:0);
        specparam PATHPULSE$ = 0;
                                                                                 
    endspecify

`endif
    
endmodule

`endcelldefine

