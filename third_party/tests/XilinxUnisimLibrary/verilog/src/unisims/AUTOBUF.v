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
//  /   /                  Clock Buffer
// /___/   /\     Filename : AUTOBUF.v
// \   \  /  \    Timestamp : 
//  \___\/\___\
//
// Revision:
//    04/08/08 - Initial version.
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
// End Revision

`timescale  1 ps / 1 ps


`celldefine

module AUTOBUF (O, I);

    parameter BUFFER_TYPE = "AUTO";

`ifdef XIL_TIMING

    parameter LOC = "UNPLACED";

`endif

    
    output O;

    input  I;

    initial begin
	
	case (BUFFER_TYPE)
	    "AUTO" : ;
	    "BUF" : ;
	    "BUFG" : ;
	    "BUFGP" : ;
	    "BUFH" : ;
	    "BUFIO" : ;
	    "BUFIO2" : ;
	    "BUFIO2FB" : ;
	    "BUFR" : ;
	    "IBUF" : ;
	    "IBUFG" : ;
	    "NONE" : ;
	    "OBUF" : ;
	    default : begin
		$display("Attribute Syntax Error : The Attribute BUFFER_TYPE on AUTOBUF instance %m is set to %s.  Legal values for this attribute are AUTO, BUF, BUFG, BUFGP, BUFH, BUFIO, BUFIO2, BUFIO2FB, BUFR, IBUF, IBUFG, NONE, and OBUF.", BUFFER_TYPE);
	    end
	endcase
	
    end

    buf B1 (O, I);
    
`ifdef XIL_TIMING

    specify

	(I => O) = (0:0:0, 0:0:0);
	specparam PATHPULSE$ = 0;
	
    endspecify

`endif
    
endmodule

`endcelldefine

