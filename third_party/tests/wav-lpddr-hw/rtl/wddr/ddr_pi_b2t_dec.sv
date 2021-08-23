
/*********************************************************************************
Copyright (c) 2021 Wavious LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*********************************************************************************/

module ddr_pi_b2t_dec #(
) (
   input  logic [5:0]  i_code_bin,
   output logic [15:0] o_code_therm,
   output logic [1:0]  o_quad
);

   //parameter integer DWIDTH = 1;
   //parameter integer BWIDTH = 6;
   parameter integer TWIDTH = 16;

   logic [TWIDTH-1:0] therm;

`ifdef DDR_PI_WRAPPER_BEHAV
//RTL Code

   always_comb begin
      case(i_code_bin[3:0])
         'd15: therm =  16'b0000_0000_0000_0001;
         'd14: therm =  16'b0000_0000_0000_0011;
         'd13: therm =  16'b0000_0000_0000_0111;
         'd12: therm =  16'b0000_0000_0000_1111;
         'd11: therm =  16'b0000_0000_0001_1111;
         'd10: therm =  16'b0000_0000_0011_1111;
          'd9: therm =  16'b0000_0000_0111_1111;
          'd8: therm =  16'b0000_0000_1111_1111;
          'd7: therm =  16'b0000_0001_1111_1111;
          'd6: therm =  16'b0000_0011_1111_1111;
          'd5: therm =  16'b0000_0111_1111_1111;
          'd4: therm =  16'b0000_1111_1111_1111;
          'd3: therm =  16'b0001_1111_1111_1111;
          'd2: therm =  16'b0011_1111_1111_1111;
          'd1: therm =  16'b0111_1111_1111_1111;
          'd0: therm =  16'b1111_1111_1111_1111;
      endcase
   end

   //xoring 16 bit therm code for a particular quadrant
   assign o_code_therm = {16{i_code_bin[4]}}^therm;
   // quadrant code out
   assign o_quad[1]    = i_code_bin[5]^i_code_bin[4];
   assign o_quad[0]    = (i_code_bin[5]);

`else
//Structural Code
   logic [3:1] dec_2;
   logic [7:1] dec_3;
   logic [TWIDTH-1:0] therm_b;

   ddr_wcm_tielo u_tiehi (.o_z(therm[0]));

   // first layer decoding
   ddr_wcm_nor u_nor_dec2_1 (.i_a(i_code_bin[0]), .i_b(i_code_bin[1]), .o_z(dec_2[1]));
   ddr_wcm_inv u_inv_dec2_2 (.i_a(i_code_bin[1]), .o_z(dec_2[2]));
   ddr_wcm_nand u_nand_dec2_3 (.i_a(i_code_bin[0]), .i_b(i_code_bin[1]), .o_z(dec_2[3]));

   //second layer decoding
   ddr_wcm_inv u_inv_bin_2 (.i_a(i_code_bin[2]), .o_z(i_code_bin_2_n));

   ddr_wcm_nand u_nand_dec3_1 (.i_a(i_code_bin_2_n), .i_b(dec_2[1]), .o_z(dec_3[1]));
   ddr_wcm_nand u_nand_dec3_2 (.i_a(i_code_bin_2_n), .i_b(dec_2[2]), .o_z(dec_3[2]));
   ddr_wcm_nand u_nand_dec3_3 (.i_a(i_code_bin_2_n), .i_b(dec_2[3]), .o_z(dec_3[3]));
   ddr_wcm_inv u_inv_dec3_4 (.i_a(i_code_bin_2_n), .o_z(dec_3[4]));
   ddr_wcm_nor u_nor_dec3_5 (.i_a(i_code_bin_2_n), .i_b(dec_2[3]), .o_z(dec_3[5]));
   ddr_wcm_nor u_nor_dec3_6 (.i_a(i_code_bin_2_n), .i_b(dec_2[2]), .o_z(dec_3[6]));
   ddr_wcm_nor u_nor_dec3_7 (.i_a(i_code_bin_2_n), .i_b(dec_2[1]), .o_z(dec_3[7]));

   //third layer decoding - thermometer code output
   ddr_wcm_and u_clk_and_7 (.i_a(i_code_bin[3]), .i_b(dec_3[1]), .o_z(therm[7]));
   ddr_wcm_and u_clk_and_6 (.i_a(i_code_bin[3]), .i_b(dec_3[2]), .o_z(therm[6]));
   ddr_wcm_and u_clk_and_5 (.i_a(i_code_bin[3]), .i_b(dec_3[3]), .o_z(therm[5]));
   ddr_wcm_and u_clk_and_4 (.i_a(i_code_bin[3]), .i_b(dec_3[4]), .o_z(therm[4]));
   ddr_wcm_and u_clk_and_1 (.i_a(i_code_bin[3]), .i_b(dec_3[5]), .o_z(therm[1]));
   ddr_wcm_and u_clk_and_2 (.i_a(i_code_bin[3]), .i_b(dec_3[6]), .o_z(therm[2]));
   ddr_wcm_and u_clk_and_3 (.i_a(i_code_bin[3]), .i_b(dec_3[7]), .o_z(therm[3]));

   ddr_wcm_inv u_inv_bin_3 (.i_a(i_code_bin[3]), .o_z(therm_8_n));
   ddr_wcm_inv u_inv_therm_8 (.i_a(therm_8_n), .o_z(therm[8]));

   ddr_wcm_or u_clk_or_15 (.i_a(i_code_bin[3]), .i_b(dec_3[1]), .o_z(therm[15]));
   ddr_wcm_or u_clk_or_14 (.i_a(i_code_bin[3]), .i_b(dec_3[2]), .o_z(therm[14]));
   ddr_wcm_or u_clk_or_13 (.i_a(i_code_bin[3]), .i_b(dec_3[3]), .o_z(therm[13]));
   ddr_wcm_or u_clk_or_12 (.i_a(i_code_bin[3]), .i_b(dec_3[4]), .o_z(therm[12]));
   ddr_wcm_or u_clk_or_9 (.i_a(i_code_bin[3]), .i_b(dec_3[5]), .o_z(therm[9]));
   ddr_wcm_or u_clk_or_10 (.i_a(i_code_bin[3]), .i_b(dec_3[6]), .o_z(therm[10]));
   ddr_wcm_or u_clk_or_11 (.i_a(i_code_bin[3]), .i_b(dec_3[7]), .o_z(therm[11]));

   //fourth layer - xoring 16 bit therm code for a particular quadrant
   genvar indxt;
   generate
      for(indxt=0;indxt<TWIDTH;indxt=indxt+1) begin: gate_clk_inv_xor
         ddr_wcm_inv u_inv_therm (.i_a(therm[indxt]), .o_z(therm_b[indxt]));
         ddr_wcm_xor u_clk_xor   (.i_a(i_code_bin[4]), .i_b(therm_b[indxt]), .o_z(o_code_therm[indxt]));
      end
   endgenerate

   //quadrant code out
   ddr_wcm_xor u_quad_xor (.i_a(i_code_bin[4]), .i_b(i_code_bin[5]), .o_z(o_quad[1]));
   assign o_quad[0]      = i_code_bin[5];

`endif

endmodule
