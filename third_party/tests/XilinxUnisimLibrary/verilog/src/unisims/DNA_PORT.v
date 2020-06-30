///////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2004 Xilinx, Inc.
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
// \   \   \/     Version : 8.1i
//  \   \         Description : Xilinx Timing Simulation Library Component
//  /   /                       Device DNA Data Access Port
// /___/   /\     Filename : DNA_PORT.v
// \   \  /  \    Timestamp : Mon Oct 10 14:55:34 PDT 2005
//  \___\/\___\
//
// Revision:
//    10/10/05 - Initial version.
//    05/29/07 - Added wire declaration for internal signals
//    04/07/08 - CR 469973 -- Header Description fix
//    06/04/08 - CR 472697 -- added check for SIM_DNA_VALUE[56:55] 
//    09/18/08 - CR 488646 -- added period check for simprim 
//    10/28/08 - IR 494079 -- Shifting of dna_value is corrected to MSB first out
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//    07/27/12 - Removed DRC warning for SIM_DNA_VALUE (CR 669726).
//    01/21/15 - Update to 7 series behavior (PR 841966).
// End Revision

`timescale  1 ps / 1 ps

`celldefine

module DNA_PORT (DOUT, CLK, DIN, READ, SHIFT);

    parameter [56:0] SIM_DNA_VALUE = 57'h0;


`ifdef XIL_TIMING

    parameter LOC = "UNPLACED";

`endif


    output DOUT;

    input  CLK, DIN, READ, SHIFT;

    tri0  GSR = glbl.GSR;

    localparam MAX_DNA_BITS = 57;
    localparam MSB_DNA_BITS = MAX_DNA_BITS - 1;

    reg [MSB_DNA_BITS:0] dna_val = SIM_DNA_VALUE;
    reg dout_out;
    reg notifier;

    wire clk_in, din_in, gsr_in, read_in, shift_in;

    buf b_dout  (DOUT, dout_out);
    buf b_clk   (clk_in, CLK);
    buf b_din   (din_in, DIN);
    buf buf_gsr (gsr_in, GSR);
    buf b_read  (read_in, READ);
    buf b_shift (shift_in, SHIFT);


//  GSR has no effect
    
    always @(posedge clk_in) begin
       if(read_in == 1'b1) begin
          dna_val = SIM_DNA_VALUE;
	  dout_out = dna_val[MSB_DNA_BITS];
       end // read_in == 1'b1
       else if(read_in == 1'b0)
               if(shift_in == 1'b1) begin
// IR 494079
//                   dna_val = {din_in, dna_val[MSB_DNA_BITS :1]};
                   dna_val = {dna_val[MSB_DNA_BITS-1 : 0], din_in};
                   dout_out = dna_val[MSB_DNA_BITS];
               end  // shift_in == 1'b1
    end // always @ (posedge clk_in)


    specify

	(CLK => DOUT) = (100:100:100, 100:100:100);
	
`ifdef XIL_TIMING

        $period (posedge CLK, 0:0:0, notifier);
        $setuphold (posedge CLK, posedge DIN, 0:0:0, 0:0:0, notifier);
        $setuphold (posedge CLK, negedge DIN, 0:0:0, 0:0:0, notifier);
        $setuphold (posedge CLK, posedge READ, 0:0:0, 0:0:0, notifier);
        $setuphold (posedge CLK, negedge READ, 0:0:0, 0:0:0, notifier);
        $setuphold (posedge CLK, posedge SHIFT, 0:0:0, 0:0:0, notifier);
        $setuphold (posedge CLK, negedge SHIFT, 0:0:0, 0:0:0, notifier);

`endif
    
        specparam PATHPULSE$ = 0;

    endspecify
    

endmodule // DNA_PORT

`endcelldefine
