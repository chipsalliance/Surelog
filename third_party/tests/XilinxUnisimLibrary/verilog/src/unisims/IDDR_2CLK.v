///////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2006 Xilinx, Inc.
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
//  /   /                  Input Dual Data-Rate Register with Dual Clock inputs
// /___/   /\     Filename : IDDR_2CLK.v
// \   \  /  \    Timestamp : Mon Jun 26 16:44:06 PST 2006
//  \___\/\___\
//
// Revision:
//    06/26/06 - Initial version.
//    05/29/07 - Added wire declaration for internal signals
//    04/15/08 - CR 468871 Negative SetupHold fix
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//    08/23/13 - PR683925 - add invertible pin support.
//    10/22/14 - Added #1 to $finish (CR 808642).
// End Revision

`timescale  1 ps / 1 ps

`celldefine

module IDDR_2CLK (Q1, Q2, C, CB, CE, D, R, S);

    parameter DDR_CLK_EDGE = "OPPOSITE_EDGE";    
    parameter INIT_Q1 = 1'b0;
    parameter INIT_Q2 = 1'b0;
    parameter [0:0] IS_CB_INVERTED = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b0;
    parameter [0:0] IS_D_INVERTED = 1'b0;
    parameter SRTYPE = "SYNC";

  `ifdef XIL_TIMING
     parameter LOC = "UNPLACED";
  `endif

    output Q1;
    output Q2;
    
    input C;
    input CB;
    input CE;
    input D;
    input R;
    input S;

    reg q1_out = INIT_Q1, q2_out = INIT_Q2;
    reg q1_out_int, q2_out_int;
    reg q1_out_pipelined, q2_out_same_edge_int;
    reg notifier, notifier1, notifier2;
    
    wire c_in,delay_c;
    wire cb_in,delay_cb;
    wire ce_in,delay_ce;
    wire d_in,delay_d;
    wire gsr_in;
    wire r_in,delay_r;
    wire s_in,delay_s;

    tri0 GSR = glbl.GSR;

    `ifndef XIL_TIMING
    assign delay_c = C;
    assign delay_cb = CB;
    assign delay_ce = CE;
    assign delay_d = D;
    assign delay_r = R;
    assign delay_s = S;
    `endif

    //buf buf_c (c_in, C);
    //buf buf_cb (cb_in, CB);
    assign c_in = IS_C_INVERTED ^ delay_c;
    assign cb_in = (CB === 1'bz) || (IS_CB_INVERTED ^ delay_cb); // rv 1

    buf buf_ce (ce_in, delay_ce);
    //buf buf_d (d_in, D);
    assign d_in = IS_D_INVERTED ^ delay_d;
    buf buf_gsr (gsr_in, GSR);
    buf buf_q1 (Q1, q1_out);
    buf buf_q2 (Q2, q2_out);
    buf buf_r (r_in, delay_r);
    buf buf_s (s_in, delay_s);    


   initial begin

      if ((INIT_Q1 != 0) && (INIT_Q1 != 1)) begin
	 $display("Attribute Syntax Error : The attribute INIT_Q1 on IDDR_2CLK instance %m is set to %d.  Legal values for this attribute are 0 or 1.", INIT_Q1);
	 #1 $finish;
      end
      
      if ((INIT_Q2 != 0) && (INIT_Q2 != 1)) begin
	 $display("Attribute Syntax Error : The attribute INIT_Q1 on IDDR_2CLK instance %m is set to %d.  Legal values for this attribute are 0 or 1.", INIT_Q2);
	 #1 $finish;
      end
      
      if ((DDR_CLK_EDGE != "OPPOSITE_EDGE") && (DDR_CLK_EDGE != "SAME_EDGE") && (DDR_CLK_EDGE != "SAME_EDGE_PIPELINED")) begin
	 $display("Attribute Syntax Error : The attribute DDR_CLK_EDGE on IDDR_2CLK instance %m is set to %s.  Legal values for this attribute are OPPOSITE_EDGE, SAME_EDGE or SAME_EDGE_PIPELINED.", DDR_CLK_EDGE);
	 #1 $finish;
      end
      
      if ((SRTYPE != "ASYNC") && (SRTYPE != "SYNC")) begin
	 $display("Attribute Syntax Error : The attribute SRTYPE on IDDR_2CLK instance %m is set to %s.  Legal values for this attribute are ASYNC or SYNC.", SRTYPE);
	 #1 $finish;
      end
      
   end // initial begin
    
         
    always @(gsr_in or r_in or s_in) begin
   if (gsr_in == 1'b1) begin
       assign q1_out_int = INIT_Q1;
       assign q1_out_pipelined = INIT_Q1;
       assign q2_out_same_edge_int = INIT_Q2;
       assign q2_out_int = INIT_Q2;
   end
   else if (gsr_in == 1'b0) begin
       if (r_in == 1'b1 && SRTYPE == "ASYNC") begin
      assign q1_out_int = 1'b0;
      assign q1_out_pipelined = 1'b0;
      assign q2_out_same_edge_int = 1'b0;
      assign q2_out_int = 1'b0;
       end
            else if (r_in == 1'b0 && s_in == 1'b1 && SRTYPE == "ASYNC") begin
      assign q1_out_int = 1'b1;
      assign q1_out_pipelined = 1'b1;
      assign q2_out_same_edge_int = 1'b1;
      assign q2_out_int = 1'b1;
       end
       else if ((r_in == 1'b1 || s_in == 1'b1) && SRTYPE == "SYNC") begin
      deassign q1_out_int;
      deassign q1_out_pipelined;
      deassign q2_out_same_edge_int;
      deassign q2_out_int;
       end       
       else if (r_in == 1'b0 && s_in == 1'b0) begin
      deassign q1_out_int;
      deassign q1_out_pipelined;
      deassign q2_out_same_edge_int;
      deassign q2_out_int;
       end
   end // if (gsr_in == 1'b0)
    end // always @ (gsr_in or r_in or s_in)
    
       
    always @(posedge c_in) begin
    if (r_in == 1'b1) begin
       q1_out_int <= 1'b0;
       q1_out_pipelined <= 1'b0;
       q2_out_same_edge_int <= 1'b0;
   end
   else if (r_in == 1'b0 && s_in == 1'b1) begin
       q1_out_int <= 1'b1;
       q1_out_pipelined <= 1'b1;
       q2_out_same_edge_int <= 1'b1;
   end
   else if (ce_in == 1'b1 && r_in == 1'b0 && s_in == 1'b0) begin
            q1_out_int <= d_in;
       q1_out_pipelined <= q1_out_int;
       q2_out_same_edge_int <= q2_out_int;
   end
    end // always @ (posedge c_in)
    
   
    always @(posedge cb_in) begin
   if (r_in == 1'b1)
       q2_out_int <= 1'b0;
   else if (r_in == 1'b0 && s_in == 1'b1)
       q2_out_int <= 1'b1;
   else if (ce_in == 1'b1 && r_in == 1'b0 && s_in == 1'b0)
       q2_out_int <= d_in;
    end // always @ (posedge cb_in)
    
    
    always @(posedge c_in or posedge cb_in, q1_out_int or q2_out_int or q2_out_same_edge_int or q1_out_pipelined) begin
   case (DDR_CLK_EDGE)
       "OPPOSITE_EDGE" : begin
                        q1_out <= q1_out_int;
                        q2_out <= q2_out_int;
                         end
       "SAME_EDGE" : begin
                         q1_out <= q1_out_int;
                         q2_out <= q2_out_same_edge_int;
                     end
       "SAME_EDGE_PIPELINED" : begin
                              q1_out <= q1_out_pipelined;
                                     q2_out <= q2_out_same_edge_int;
                               end
       default : begin
                       $display("Attribute Syntax Error : The attribute DDR_CLK_EDGE on IDDR_2CLK instance %m is set to %s.  Legal values for this attribute are OPPOSITE_EDGE, SAME_EDGE or SAME_EDGE_PIPELINED.", DDR_CLK_EDGE);
                $finish;
       end
   endcase // case(DDR_CLK_EDGE)
    end // always @ (q1_out_int or q2_out_int or q2_out_same_edge_int or q1_out_pipelined or q2_out_pipelined)

`ifndef XIL_TIMING
    specify

        (C => Q1)  = (100, 100);
        (C => Q2)  = (100, 100);
        (CB => Q1) = (100, 100);
        (CB => Q2) = (100, 100);
	(posedge R => (Q1 +: 0)) = (0:0:0, 0:0:0);
        (posedge R => (Q2 +: 0)) = (0:0:0, 0:0:0);
        (posedge S => (Q1 +: 0)) = (0:0:0, 0:0:0);
        (posedge S => (Q2 +: 0)) = (0:0:0, 0:0:0);

        specparam PATHPULSE$ = 0;

    endspecify
`endif //  `ifndef XIL_TIMING

`ifdef XIL_TIMING

//*** Timing Checks Start here

    always @(notifier or notifier1) begin
   q1_out <= 1'bx;
    end
    
    always @(notifier or notifier2) begin
   q2_out <= 1'bx;
    end
   wire c_en_n;
   wire c_en_p;
   wire cb_en_n;
   wire cb_en_p;
   assign c_en_n = IS_C_INVERTED;
   assign c_en_p = ~IS_C_INVERTED;
   assign cb_en_n = IS_CB_INVERTED;
   assign cb_en_p = ~IS_CB_INVERTED;

    specify
   
   (C => Q1)  = (100:100:100, 100:100:100);
   (C => Q2)  = (100:100:100, 100:100:100);
   (CB => Q1) = (100:100:100, 100:100:100);
   (CB => Q2) = (100:100:100, 100:100:100);
   (R => Q1)  = (0:0:0, 0:0:0);
   (R => Q2)  = (0:0:0, 0:0:0);
   (S => Q1)  = (0:0:0, 0:0:0);
   (S => Q2)  = (0:0:0, 0:0:0);
   (posedge R => (Q1 +: 0)) = (0:0:0, 0:0:0);
   (posedge R => (Q2 +: 0)) = (0:0:0, 0:0:0);
   (posedge S => (Q1 +: 0)) = (0:0:0, 0:0:0);
   (posedge S => (Q2 +: 0)) = (0:0:0, 0:0:0);
   $period (negedge C, 0:0:0, notifier);
   $period (negedge CB, 0:0:0, notifier);
   $period (posedge C, 0:0:0, notifier);
   $period (posedge CB, 0:0:0, notifier);
   $recrem (negedge R, negedge C, 0:0:0, 0:0:0, notifier1, c_en_n, c_en_n);
   $recrem (negedge R, negedge CB, 0:0:0, 0:0:0, notifier2, cb_en_n, cb_en_n);
   $recrem (negedge R, posedge C, 0:0:0, 0:0:0, notifier1, c_en_p, c_en_p);
   $recrem (negedge R, posedge CB, 0:0:0, 0:0:0, notifier2, cb_en_p, cb_en_p);
   $recrem (negedge S, negedge C, 0:0:0, 0:0:0, notifier1, c_en_n, c_en_n);
   $recrem (negedge S, negedge CB, 0:0:0, 0:0:0, notifier2, cb_en_n, cb_en_n);
   $recrem (negedge S, posedge C, 0:0:0, 0:0:0, notifier1, c_en_p, c_en_p);
   $recrem (negedge S, posedge CB, 0:0:0, 0:0:0, notifier2, cb_en_p, cb_en_p);
    $recrem ( posedge R, negedge C, 0:0:0, 0:0:0, notifier1, c_en_n, c_en_n);
    $recrem ( posedge R, negedge CB, 0:0:0, 0:0:0, notifier2, cb_en_n, cb_en_n);
    $recrem ( posedge R, posedge C, 0:0:0, 0:0:0, notifier1, c_en_p, c_en_p);
    $recrem ( posedge R, posedge CB, 0:0:0, 0:0:0, notifier2, cb_en_p, cb_en_p);
    $recrem ( posedge S, negedge C, 0:0:0, 0:0:0, notifier1, c_en_n, c_en_n);
    $recrem ( posedge S, negedge CB, 0:0:0, 0:0:0, notifier2, cb_en_n, cb_en_n);
    $recrem ( posedge S, posedge C, 0:0:0, 0:0:0, notifier1, c_en_p, c_en_p);
    $recrem ( posedge S, posedge CB, 0:0:0, 0:0:0, notifier2, cb_en_p, cb_en_p);
   $setuphold (negedge C,  negedge CE, 0:0:0, 0:0:0, notifier1, c_en_n, c_en_n, delay_c,  delay_ce);
   $setuphold (negedge C,  negedge D,  0:0:0, 0:0:0, notifier1, c_en_n, c_en_n, delay_c,  delay_d);
   $setuphold (negedge C,  negedge R,  0:0:0, 0:0:0, notifier1, c_en_n, c_en_n, delay_c,  delay_r);
   $setuphold (negedge C,  negedge S,  0:0:0, 0:0:0, notifier1, c_en_n, c_en_n, delay_c,  delay_s);
   $setuphold (negedge C,  posedge CE, 0:0:0, 0:0:0, notifier1, c_en_n, c_en_n, delay_c,  delay_ce);
   $setuphold (negedge C,  posedge D,  0:0:0, 0:0:0, notifier1, c_en_n, c_en_n, delay_c,  delay_d);
   $setuphold (negedge C,  posedge R,  0:0:0, 0:0:0, notifier1, c_en_n, c_en_n, delay_c,  delay_r);
   $setuphold (negedge C,  posedge S,  0:0:0, 0:0:0, notifier1, c_en_n, c_en_n, delay_c,  delay_s);
   $setuphold (negedge CB, negedge CE, 0:0:0, 0:0:0, notifier2, cb_en_n, cb_en_n, delay_cb, delay_ce);
   $setuphold (negedge CB, negedge D,  0:0:0, 0:0:0, notifier2, cb_en_n, cb_en_n, delay_cb, delay_d);
   $setuphold (negedge CB, negedge R,  0:0:0, 0:0:0, notifier2, cb_en_n, cb_en_n, delay_cb, delay_r);
   $setuphold (negedge CB, negedge S,  0:0:0, 0:0:0, notifier2, cb_en_n, cb_en_n, delay_cb, delay_s);
   $setuphold (negedge CB, posedge CE, 0:0:0, 0:0:0, notifier2, cb_en_n, cb_en_n, delay_cb, delay_ce);
   $setuphold (negedge CB, posedge D,  0:0:0, 0:0:0, notifier2, cb_en_n, cb_en_n, delay_cb, delay_d);
   $setuphold (negedge CB, posedge R,  0:0:0, 0:0:0, notifier2, cb_en_n, cb_en_n, delay_cb, delay_r);
   $setuphold (negedge CB, posedge S,  0:0:0, 0:0:0, notifier2, cb_en_n, cb_en_n, delay_cb, delay_s);
   $setuphold (posedge C,  negedge CE, 0:0:0, 0:0:0, notifier1, c_en_p, c_en_p, delay_c,  delay_ce);
   $setuphold (posedge C,  negedge D,  0:0:0, 0:0:0, notifier1, c_en_p, c_en_p, delay_c,  delay_d);
   $setuphold (posedge C,  negedge R,  0:0:0, 0:0:0, notifier1, c_en_p, c_en_p, delay_c,  delay_r);
   $setuphold (posedge C,  negedge S,  0:0:0, 0:0:0, notifier1, c_en_p, c_en_p, delay_c,  delay_s);
   $setuphold (posedge C,  posedge CE, 0:0:0, 0:0:0, notifier1, c_en_p, c_en_p, delay_c,  delay_ce);
   $setuphold (posedge C,  posedge D,  0:0:0, 0:0:0, notifier1, c_en_p, c_en_p, delay_c,  delay_d);
   $setuphold (posedge C,  posedge R,  0:0:0, 0:0:0, notifier1, c_en_p, c_en_p, delay_c,  delay_r);
   $setuphold (posedge C,  posedge S,  0:0:0, 0:0:0, notifier1, c_en_p, c_en_p, delay_c,  delay_s);
   $setuphold (posedge CB, negedge CE, 0:0:0, 0:0:0, notifier2, cb_en_p, cb_en_p, delay_cb, delay_ce);
   $setuphold (posedge CB, negedge D,  0:0:0, 0:0:0, notifier2, cb_en_p, cb_en_p, delay_cb, delay_d);
   $setuphold (posedge CB, negedge R,  0:0:0, 0:0:0, notifier2, cb_en_p, cb_en_p, delay_cb, delay_r);
   $setuphold (posedge CB, negedge S,  0:0:0, 0:0:0, notifier2, cb_en_p, cb_en_p, delay_cb, delay_s);
   $setuphold (posedge CB, posedge CE, 0:0:0, 0:0:0, notifier2, cb_en_p, cb_en_p, delay_cb, delay_ce);
   $setuphold (posedge CB, posedge D,  0:0:0, 0:0:0, notifier2, cb_en_p, cb_en_p, delay_cb, delay_d);
   $setuphold (posedge CB, posedge R,  0:0:0, 0:0:0, notifier2, cb_en_p, cb_en_p, delay_cb, delay_r);
   $setuphold (posedge CB, posedge S,  0:0:0, 0:0:0, notifier2, cb_en_p, cb_en_p, delay_cb, delay_s);
   $width (negedge C, 0:0:0, 0, notifier);
   $width (negedge CB, 0:0:0, 0, notifier);
   $width (negedge R, 0:0:0, 0, notifier);
   $width (negedge S, 0:0:0, 0, notifier);
   $width (posedge C, 0:0:0, 0, notifier);
   $width (posedge CB, 0:0:0, 0, notifier);
   $width (posedge R, 0:0:0, 0, notifier);
   $width (posedge S, 0:0:0, 0, notifier);

   specparam PATHPULSE$ = 0;
   
    endspecify
`endif //  `ifdef XIL_TIMING


endmodule // IDDR_2CLK

`endcelldefine
