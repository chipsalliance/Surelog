// ========== Copyright Header Begin ==========================================
// 
// OpenSPARC T1 Processor File: flop_rptrs_xc2.v
// Copyright (c) 2006 Sun Microsystems, Inc.  All Rights Reserved.
// DO NOT ALTER OR REMOVE COPYRIGHT NOTICES.
// 
// The above named program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public
// License version 2 as published by the Free Software Foundation.
// 
// The above named program is distributed in the hope that it will be 
// useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// General Public License for more details.
// 
// You should have received a copy of the GNU General Public
// License along with this work; if not, write to the Free Software
// Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA.
// 
// ========== Copyright Header End ============================================

module flop_rptrs_xc2(/*AUTOARG*/
   // Outputs
   sparc_out, so, jbussync2_out, jbussync1_out, grst_out, 
   gdbginit_out, ddrsync2_out, ddrsync1_out, cken_out, 
   // Inputs
   spare_in, se, sd, jbussync2_in, jbussync1_in, grst_in, 
   gdbginit_in, gclk, ddrsync2_in, ddrsync1_in, cken_in, agrst_l, 
   adbginit_l
   );

   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [25:0]        cken_out;               // From cken_ff_25_ of bw_u1_soffasr_2x.v, ...
   output               ddrsync1_out;           // From ddrsync1_ff of bw_u1_soffasr_2x.v
   output               ddrsync2_out;           // From ddrsync2_ff of bw_u1_soffasr_2x.v
   output               gdbginit_out;           // From gdbginit_ff of bw_u1_soffasr_2x.v
   output               grst_out;               // From gclk_ff of bw_u1_soffasr_2x.v
   output               jbussync1_out;          // From jbussync1_ff of bw_u1_soffasr_2x.v
   output               jbussync2_out;          // From jbussync2_ff of bw_u1_soffasr_2x.v
   output               so;                     // From scanout_latch of bw_u1_scanlg_2x.v
   output [5:0]         sparc_out;              // From spare_ff_5_ of bw_u1_soffasr_2x.v, ...
   // End of automatics

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input                adbginit_l;             // To gdbginit_ff of bw_u1_soffasr_2x.v
   input                agrst_l;                // To spare_ff_5_ of bw_u1_soffasr_2x.v, ...
   input [25:0]         cken_in;                // To cken_ff_25_ of bw_u1_soffasr_2x.v, ...
   input                ddrsync1_in;            // To ddrsync1_ff of bw_u1_soffasr_2x.v
   input                ddrsync2_in;            // To ddrsync2_ff of bw_u1_soffasr_2x.v
   input                gclk;                   // To I73 of bw_u1_ckbuf_33x.v
   input                gdbginit_in;            // To gdbginit_ff of bw_u1_soffasr_2x.v
   input                grst_in;                // To gclk_ff of bw_u1_soffasr_2x.v
   input                jbussync1_in;           // To jbussync1_ff of bw_u1_soffasr_2x.v
   input                jbussync2_in;           // To jbussync2_ff of bw_u1_soffasr_2x.v
   input                sd;                     // To spare_ff_5_ of bw_u1_soffasr_2x.v
   input                se;                     // To spare_ff_5_ of bw_u1_soffasr_2x.v, ...
   input [5:0]          spare_in;               // To spare_ff_5_ of bw_u1_soffasr_2x.v, ...
   // End of automatics
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire                 clk;                    // From I73 of bw_u1_ckbuf_33x.v
   wire                 scan_data_0;            // From spare_ff_5_ of bw_u1_soffasr_2x.v
   wire                 scan_data_1;            // From spare_ff_4_ of bw_u1_soffasr_2x.v
   wire                 scan_data_10;           // From gdbginit_ff of bw_u1_soffasr_2x.v
   wire                 scan_data_11;           // From gclk_ff of bw_u1_soffasr_2x.v
   wire                 scan_data_2;            // From spare_ff_3_ of bw_u1_soffasr_2x.v
   wire                 scan_data_3;            // From spare_ff_2_ of bw_u1_soffasr_2x.v
   wire                 scan_data_4;            // From spare_ff_1_ of bw_u1_soffasr_2x.v
   wire                 scan_data_5;            // From spare_ff_0_ of bw_u1_soffasr_2x.v
   wire                 scan_data_6;            // From jbussync2_ff of bw_u1_soffasr_2x.v
   wire                 scan_data_7;            // From jbussync1_ff of bw_u1_soffasr_2x.v
   wire                 scan_data_8;            // From ddrsync2_ff of bw_u1_soffasr_2x.v
   wire                 scan_data_9;            // From ddrsync1_ff of bw_u1_soffasr_2x.v
   // End of automatics

   /* bw_u1_ckbuf_33x AUTO_TEMPLATE (
    .clk                                (clk ),
    .rclk                               (gclk ) ); */
   
   bw_u1_ckbuf_33x I73
   (/*AUTOINST*/
    // Outputs
    .clk                                (clk ),                  // Templated
    // Inputs
    .rclk                               (gclk ));                 // Templated
   
   /* bw_u1_soffasr_2x AUTO_TEMPLATE (
    .q                                  (sparc_out[@]),
    .d                                  (spare_in[@]),
    .ck                                 (clk ),
    .r_l                                (agrst_l ),
    .s_l                                (1'b1),
    .sd                                 (scan_data_@"(- 4 @)" ),
    .so                                 (scan_data_@"(- 5 @)" ),
    ); */

   bw_u1_soffasr_2x spare_ff_5_
   (
    // Inputs
    .sd                                 (sd ),
    /*AUTOINST*/
    // Outputs
    .q                                  (sparc_out[5]),          // Templated
    .so                                 (scan_data_0 ),          // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (spare_in[5]),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (se));

   bw_u1_soffasr_2x spare_ff_4_
   (
    /*AUTOINST*/
    // Outputs
    .q                                  (sparc_out[4]),          // Templated
    .so                                 (scan_data_1 ),          // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (spare_in[4]),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (se),
    .sd                                 (scan_data_0 ));          // Templated
   
   bw_u1_soffasr_2x spare_ff_3_
   (
    /*AUTOINST*/
    // Outputs
    .q                                  (sparc_out[3]),          // Templated
    .so                                 (scan_data_2 ),          // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (spare_in[3]),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (se),
    .sd                                 (scan_data_1 ));          // Templated

   bw_u1_soffasr_2x spare_ff_2_
   (
    /*AUTOINST*/
    // Outputs
    .q                                  (sparc_out[2]),          // Templated
    .so                                 (scan_data_3 ),          // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (spare_in[2]),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (se),
    .sd                                 (scan_data_2 ));          // Templated

   bw_u1_soffasr_2x spare_ff_1_
   (
    /*AUTOINST*/
    // Outputs
    .q                                  (sparc_out[1]),          // Templated
    .so                                 (scan_data_4 ),          // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (spare_in[1]),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (se),
    .sd                                 (scan_data_3 ));          // Templated

   bw_u1_soffasr_2x spare_ff_0_
   (
    /*AUTOINST*/
    // Outputs
    .q                                  (sparc_out[0]),          // Templated
    .so                                 (scan_data_5 ),          // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (spare_in[0]),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (se),
    .sd                                 (scan_data_4 ));          // Templated

   /* bw_u1_soffasr_2x AUTO_TEMPLATE (
     .q                                 (cken_out[@] ),
     .d                                 (cken_in[@] ),
     .ck                                (clk ),
     .r_l                               (agrst_l ),
     .s_l                               (1'b1),
     .se                                (1'b0),
     .sd                                (1'b0),
     .so                                (),
     ); */

   bw_u1_soffasr_2x cken_ff_25_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[25] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[25] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_24_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[24] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[24] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated
   
   bw_u1_soffasr_2x cken_ff_23_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[23] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[23] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_22_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[22] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[22] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_21_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[21] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[21] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_20_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[20] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[20] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_19_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[19] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[19] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_18_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[18] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[18] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_17_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[17] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[17] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_16_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[16] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[16] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_15_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[15] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[15] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_14_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[14] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[14] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_13_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[13] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[13] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_12_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[12] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[12] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_11_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[11] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[11] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_10_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[10] ),         // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[10] ),          // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_9_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[9] ),          // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[9] ),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_8_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[8] ),          // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[8] ),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_7_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[7] ),          // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[7] ),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_6_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[6] ),          // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[6] ),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_5_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[5] ),          // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[5] ),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_4_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[4] ),          // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[4] ),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_3_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[3] ),          // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[3] ),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_2_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[2] ),          // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[2] ),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_1_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[1] ),          // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[1] ),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   bw_u1_soffasr_2x cken_ff_0_
   ( /*AUTOINST*/
    // Outputs
    .q                                  (cken_out[0] ),          // Templated
    .so                                 (),                      // Templated
    // Inputs
    .ck                                 (clk ),                  // Templated
    .d                                  (cken_in[0] ),           // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (1'b0),                  // Templated
    .sd                                 (1'b0));                  // Templated

   /* bw_u1_soffasr_2x AUTO_TEMPLATE (
     .ck                                (clk ),
     .r_l                               (agrst_l ),
     .s_l                               (1'b1),
     .se                                (se ),
     ); */

   bw_u1_soffasr_2x ddrsync1_ff
   (
    // Outputs
    .q                                  (ddrsync1_out ),
    .so                                 (scan_data_9 ),
    // Inputs
    .d                                  (ddrsync1_in ),
    .sd                                 (scan_data_8 ),
    /*AUTOINST*/
    // Inputs
    .ck                                 (clk ),                  // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (se ));                   // Templated

   bw_u1_soffasr_2x ddrsync2_ff 
   (
    // Outputs
    .q                                  (ddrsync2_out ),
    .so                                 (scan_data_8 ),
    // Inputs
    .d                                  (ddrsync2_in ),
    .sd                                 (scan_data_7 ),
    /*AUTOINST*/
    // Inputs
    .ck                                 (clk ),                  // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (se ));                   // Templated

   bw_u1_soffasr_2x jbussync1_ff
   (
    // Outputs
    .q                                  (jbussync1_out ),
    .so                                 (scan_data_7 ),
    // Inputs
    .d                                  (jbussync1_in ),
    .sd                                 (scan_data_6 ),
    /*AUTOINST*/
    // Inputs
    .ck                                 (clk ),                  // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (se ));                   // Templated

   bw_u1_soffasr_2x jbussync2_ff
   (
    // Outputs
    .q                                  (jbussync2_out ),
    .so                                 (scan_data_6 ),
    // Inputs
    .d                                  (jbussync2_in ),
    .sd                                 (scan_data_5 ),
    /*AUTOINST*/
    // Inputs
    .ck                                 (clk ),                  // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (se ));                   // Templated

   bw_u1_soffasr_2x gdbginit_ff
   (
    // Outputs
    .q                                  (gdbginit_out ),
    .so                                 (scan_data_10 ),
    // Inputs
    .d                                  (gdbginit_in ),
    .sd                                 (scan_data_9 ),
    .r_l                                (adbginit_l),
    /*AUTOINST*/
    // Inputs
    .ck                                 (clk ),                  // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (se ));                   // Templated

   bw_u1_soffasr_2x gclk_ff
   (
    // Outputs
    .q                                  (grst_out ),
    .so                                 (scan_data_11 ),
    // Inputs
    .d                                  (grst_in ),
    .sd                                 (scan_data_10 ),
    /*AUTOINST*/
    // Inputs
    .ck                                 (clk ),                  // Templated
    .r_l                                (agrst_l ),              // Templated
    .s_l                                (1'b1),                  // Templated
    .se                                 (se ));                   // Templated

   /* bw_u1_scanlg_2x AUTO_TEMPLATE (
     .sd                                (scan_data_11 ),
     .ck                                (clk ),
     ); */ 

   bw_u1_scanlg_2x scanout_latch
   ( /*AUTOINST*/
    // Outputs
    .so                                 (so),
    // Inputs
    .sd                                 (scan_data_11 ),         // Templated
    .ck                                 (clk ),                  // Templated
    .se                                 (1'b1));

endmodule

// Local Variables:
// verilog-library-files:("../../../common/rtl/u1.behV" )
// End:
