///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 2013 Xilinx Inc.
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
//
//   ____   ___
//  /   /\/   / 
// /___/  \  /     Vendor      : Xilinx 
// \   \   \/      Version     : 2013.2
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        
// /___/   /\      Filename    : DNA_PORTE2.v
// \   \  /  \ 
//  \___\/\___\                    
//                                 
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//     06/07/13 - Initial version.
//     08/27/13 - Added timing support.
//     01/21/14 - Added missing timing (CR 767382).
//     05/28/14 - New simulation library message format.
//     10/02/14 - Fixed shift in order.
//    10/22/14 - Added #1 to $finish (CR 808642).
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps 
//`celldefine

module DNA_PORTE2 #(
  `ifdef XIL_TIMING //Simprim 
  parameter LOC = "UNPLACED",  
  `endif
  parameter [95:0] SIM_DNA_VALUE = 96'h000000000000000000000000
)(
  output DOUT,

  input CLK,
  input DIN,
  input READ,
  input SHIFT
);
  
   reg [95:0] SIM_DNA_VALUE_reg = SIM_DNA_VALUE;

   // include dynamic registers - XILINX test only
  `ifdef XIL_DR
   `include "DNA_PORTE2_dr.v"
  `endif
   
   tri0 GSR = glbl.GSR;
   
   localparam MAX_DNA_BITS = 96;
   localparam MSB_DNA_BITS = MAX_DNA_BITS - 1;
   
   reg [MSB_DNA_BITS:0] dna_val = SIM_DNA_VALUE;
   reg dout_out;

  `ifdef XIL_TIMING //Simprim 
   reg notifier;
  `endif
   
   wire clk_in;
   wire din_in;
   wire read_in;
   wire shift_in;
   wire clk_delay;
   wire din_delay;
   wire read_delay;
   wire shift_delay;
   localparam MODULE_NAME = "DNA_PORTE2";

   assign DOUT = dout_out;

`ifdef XIL_TIMING // inputs with timing checks
   assign clk_in = clk_delay;
   assign din_in = din_delay;
   assign read_in = read_delay;
   assign shift_in = shift_delay;
`endif //  `ifdef XIL_TIMING

`ifndef XIL_TIMING // inputs with timing checks
   assign clk_in = CLK;
   assign din_in = DIN;
   assign read_in = READ;
   assign shift_in = SHIFT;
`endif //  `ifndef XIL_TIMING

   initial
     if ((SIM_DNA_VALUE_reg < 96'h000000000000000000000000) || (SIM_DNA_VALUE_reg > 96'hFFFFFFFFFFFFFFFFFFFFFFFD)) begin
	$display("Error: [Unisim %s-101] SIM_DNA_VALUE attribute is set to %h.  Legal values for this attribute are 96'h000000000000000000000000 to 96'hFFFFFFFFFFFFFFFFFFFFFFFD. Instance: %m", MODULE_NAME, SIM_DNA_VALUE_reg);
	#1 $finish;
     end

   
   always @(posedge clk_in) begin
      if(read_in == 1'b1) begin
         dna_val = SIM_DNA_VALUE_reg;
	 dout_out = SIM_DNA_VALUE_reg[0];
      end // read_in == 1'b1
      else if(read_in == 1'b0)
        if(shift_in == 1'b1) begin
	   dna_val = {din_in, dna_val[MSB_DNA_BITS : 1]};
	   dout_out = dna_val[0];
        end  // shift_in == 1'b1
   end // always @ (posedge clk_in)


   specify
      (CLK => DOUT) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING // Simprim
      $setuphold (posedge CLK, negedge DIN, 0:0:0, 0:0:0, notifier,,, clk_delay, din_delay);
      $setuphold (posedge CLK, negedge READ, 0:0:0, 0:0:0, notifier,,, clk_delay, read_delay);
      $setuphold (posedge CLK, negedge SHIFT, 0:0:0, 0:0:0, notifier,,, clk_delay, shift_delay);
      $setuphold (posedge CLK, posedge DIN, 0:0:0, 0:0:0, notifier,,, clk_delay, din_delay);
      $setuphold (posedge CLK, posedge READ, 0:0:0, 0:0:0, notifier,,, clk_delay, read_delay);
      $setuphold (posedge CLK, posedge SHIFT, 0:0:0, 0:0:0, notifier,,, clk_delay, shift_delay);
      $period (negedge CLK, 0:0:0, notifier);
      $period (posedge CLK, 0:0:0, notifier);
      $width (negedge CLK, 0:0:0, 0, notifier);
      $width (posedge CLK, 0:0:0, 0, notifier);
`endif
      specparam PATHPULSE$ = 0;
   endspecify
   
      
endmodule

//`endcelldefine
