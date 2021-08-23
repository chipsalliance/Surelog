
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

`include "ddr_global_define.vh"
`include "ddr_project_define.vh"

import ddr_global_pkg::*;

module ddr_inv #(
   parameter DWIDTH = 1
) (
   input  logic [DWIDTH-1:0] i_a,
   output logic [DWIDTH-1:0] o_z
);

`ifdef DDR_SLIB_TSMC12FFC
   CKND4BWP16P90CPD u_inv [DWIDTH-1:0] (
      .I  (i_a),
      .ZN (o_z)
   );
   //cadence script_begin
   //set_db -quiet [get_db insts */u_inv[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   INV_X4N_A7P5PP84TR_C16 u_inv [DWIDTH-1:0] (
      .A  (i_a),
      .Y (o_z)
   );
   //cadence script_begin
   //set_db -quiet [get_db insts */u_inv[*]] .preserve true
   //cadence script_end
`else
   assign o_z = ~i_a;
`endif

endmodule

module ddr_dly_buf #(
   parameter DWIDTH = 1
) (
   input  logic [DWIDTH-1:0] i_a,
   output logic [DWIDTH-1:0] o_z
);

`ifdef DDR_SLIB_TSMC12FFC
  //FIXME
  assign o_z = i_a ;
`elsif DDR_SLIB_GF12LPP
  DLY4_X2N_A7P5PP84TH_C18 u_dly_buf [DWIDTH-1:0] (
      .A(i_a),
      .Y(o_z)
  );
  //cadence script_begin
  //set_db -quiet [get_db insts *u_dly_buf[*]] .preserve true
  //cadence script_end
`else
   assign o_z = i_a;
`endif

endmodule

module ddr_buf #(
   parameter DWIDTH = 1
) (
   input  logic [DWIDTH-1:0] i_a,
   output logic [DWIDTH-1:0] o_z
);

`ifdef DDR_SLIB_TSMC12FFC
   logic [DWIDTH-1:0] y;

   CKND4BWP16P90CPD u_inv0 [DWIDTH-1:0] (
      .I  (i_a),
      .ZN (y)
   );
   CKND4BWP16P90CPD u_inv1 [DWIDTH-1:0] (
      .I  (y),
      .ZN (o_z)
   );
   //cadence script_begin
   //set_db -quiet [get_db insts */u_inv0[*]] .preserve true
   //set_db -quiet [get_db insts */u_inv1[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
  BUFH_X2N_A7P5PP84TR_C16 u_buf [DWIDTH-1:0] (
      .A(i_a),
      .Y(o_z)
  );
  //cadence script_begin
  //set_db -quiet [get_db insts *u_buf[*]] .preserve true
  //cadence script_end
`else
   assign o_z = i_a;
`endif

endmodule

module ddr_mux #(
   parameter DWIDTH = 1
) (
   input  logic              i_sel,
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

`ifdef DDR_SLIB_TSMC12FFC
   CKMUX2D4BWP16P90CPD u_mux [DWIDTH-1:0] (
      .I0  (i_a),
      .I1  (i_b),
      .S   (i_sel),
      .Z   (o_z)
   );

   //cadence script_begin
   //set_db -quiet [get_db insts */u_mux[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   MXT2_X4N_A7P5PP84TR_C16 u_mux [DWIDTH-1:0] (
      .A   (i_a),
      .B   (i_b),
      .S0  (i_sel),
      .Y   (o_z)
   );

   //cadence script_begin
   //set_db -quiet [get_db insts */u_mux[*]] .preserve true
   //cadence script_end
`else
   assign o_z = i_sel ? i_b : i_a;
`endif

endmodule

module ddr_latch #(
   parameter DWIDTH = 1
) (
   input  logic              i_clk,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifdef DDR_SLIB_TSMC12FFC
   LHQD0BWP16P90CPD u_latch [DWIDTH-1:0] (
      .D (i_d),
      .E (i_clk),
      .Q (o_q)
   );

   //cadence script_begin
   //set_db -quiet [get_db insts */u_latch[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   LATQ_X3N_A7P5PP84TR_C16 u_latch [DWIDTH-1:0] (
      .D   (i_d),
      .G   (i_clk),
      .Q   (o_q)
   );

   //cadence script_begin
   //set_db -quiet [get_db insts */u_latch[*]] .preserve true
   //cadence script_end
`else
   always_latch
      if (i_clk)
         o_q <= i_d;
`endif

endmodule

module ddr_latch_s #(
   parameter DWIDTH = 1
) (
   input  logic              i_clk,
   input  logic              i_set,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifdef DDR_SLIB_TSMC12FFC
   logic set_n;
   ddr_inv u_inv (.i_a(i_set), .o_z(set_n));
   LHSNQD0BWP16P90CPD u_latch [DWIDTH-1:0] (
      .SDN (set_n),
      .D   (i_d),
      .E   (i_clk),
      .Q   (o_q)
   );

   //cadence script_begin
   //set_db -quiet [get_db insts */u_latch[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   LATSPQ_X3N_A7P5PP84TR_C16 u_latch [DWIDTH-1:0] (
      .S   (i_set),
      .D   (i_d),
      .G   (i_clk),
      .Q   (o_q)
   );

   //cadence script_begin
   //set_db -quiet [get_db insts */u_latch[*]] .preserve true
   //cadence script_end
`else
   always_latch
      if (i_set)
         o_q <= '1;
      else if (i_clk)
         o_q <= i_d;
`endif
endmodule

module ddr_latch_r #(
   parameter DWIDTH = 1
) (
   input  logic              i_clk,
   input  logic              i_rst,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifdef DDR_SLIB_TSMC12FFC
   logic rst_n;
   ddr_inv u_inv (.i_a(i_rst), .o_z(rst_n));
   LHCNQD0BWP16P90CPD u_latch [DWIDTH-1:0] (
      .CDN (rst_n),
      .D   (i_d),
      .E   (i_clk),
      .Q   (o_q)
   );

   //cadence script_begin
   //set_db -quiet [get_db insts */u_latch[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   logic rst_n;
   ddr_inv u_inv (.i_a(i_rst), .o_z(rst_n));
   LATRQ_X3N_A7P5PP84TR_C16 u_latch [DWIDTH-1:0] (
      .RN  (rst_n),
      .D   (i_d),
      .G   (i_clk),
      .Q   (o_q)
   );

   //cadence script_begin
   //set_db -quiet [get_db insts */u_latch[*]] .preserve true
   //cadence script_end
`else
   always_latch
      if (i_rst)
         o_q <= '0;
      else if (i_clk)
         o_q <= i_d;
`endif

endmodule

module ddr_dff #(
   parameter DWIDTH = 1
) (
   input  logic              i_clk,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifdef DDR_SLIB_TSMC12FFC
   DFQD0BWP16P90CPD u_dff [DWIDTH-1:0] (.D(i_d), .CP(i_clk), .Q(o_q));
   //cadence script_begin
   //set_db -quiet [get_db insts */u_dff[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   DFFQ_X4N_A7P5PP84TR_C16 u_dff [DWIDTH-1:0] (.D(i_d), .CK(i_clk), .Q(o_q));
   //cadence script_begin
   //set_db -quiet [get_db insts */u_dff[*]] .preserve true
   //cadence script_end
`else
   always_ff @ (posedge i_clk)
      o_q <= i_d;
`endif

endmodule

module ddr_dff_r #(
   parameter DWIDTH = 1
) (
   input  logic              i_clk,
   input  logic              i_rst,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifdef DDR_SLIB_TSMC12FFC
   logic rst_n;
   ddr_inv u_inv (.i_a(i_rst), .o_z(rst_n));
   DFCNQD0BWP16P90CPD u_dff [DWIDTH-1:0] (.D(i_d), .CP(i_clk), .CDN(rst_n), .Q(o_q));
   //cadence script_begin
   //set_db -quiet [get_db insts */u_dff[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   DFFRPQ_X4N_A7P5PP84TR_C16 u_dff [DWIDTH-1:0] (.D(i_d), .CK(i_clk), .Q(o_q), .R(i_rst));
   //cadence script_begin
   //set_db -quiet [get_db insts */u_dff[*]] .preserve true
   //cadence script_end
`else
   always_ff @(posedge i_clk, posedge i_rst)
      if (i_rst)
         o_q <= '0;
      else
         o_q <= i_d;
`endif

endmodule

module ddr_dff_s #(
   parameter DWIDTH = 1
) (
   input  logic              i_clk,
   input  logic              i_set,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifdef DDR_SLIB_TSMC12FFC
   logic set_n;
   ddr_inv u_inv (.i_a(i_set), .o_z(set_n));
   DFSNQD0BWP16P90CPD  u_dff [DWIDTH-1:0] (.D(i_d), .SDN(set_n), .CP(i_clk), .Q(o_q));
   //cadence script_begin
   //set_db -quiet [get_db insts */u_dff[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   logic set_n;
   ddr_inv u_inv (.i_a(i_set), .o_z(set_n));
   DFFSQ_X4N_A7P5PP84TR_C16 u_dff [DWIDTH-1:0] (.D(i_d), .CK(i_clk), .Q(o_q), .SN(set_n));
   //cadence script_begin
   //set_db -quiet [get_db insts */u_dff[*]] .preserve true
   //cadence script_end
`else
   always_ff @(posedge i_clk, posedge i_set)
      if (i_set)
         o_q <= '1;
      else
         o_q <= i_d;
`endif
endmodule

module ddr_dff_r_e #(
   parameter DWIDTH = 1
) (
   input  logic              i_clk,
   input  logic              i_rst,
   input  logic              i_en,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifdef DDR_SLIB_TSMC12FFC
   logic rst_n;
   ddr_inv u_inv (.i_a(i_rst), .o_z(rst_n));
   EDFCNQD1BWP16P90CPD u_dff [DWIDTH-1:0] (.D(i_d), .E(i_en), .CDN(rst_n), .CP(i_clk), .Q(o_q));
   //cadence script_begin
   //set_db -quiet [get_db insts */u_dff[*]] .preserve true
   //cadence script_end
// FIXME
//`elsif DDR_SLIB_GF12LPP
//   DFFSQ_X4N_A7P5PP84TR_C16 u_dff [DWIDTH-1:0] (.D(i_d), .CK(i_clk), .Q(o_q), .SN(set_n));
//   //cadence script_begin
//   //set_db -quiet [get_db insts */u_dff[*]] .preserve true
//   //cadence script_end
`else
   always_ff @(posedge i_clk, posedge i_rst)
      if (i_rst)
         o_q <= '0;
      else if (i_en)
         o_q <= i_d;
`endif

endmodule

module ddr_nand #(
   parameter DWIDTH = 1,
   parameter PS_DLY = 0
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

`ifdef DDR_SLIB_TSMC12FFC
   CKND2D1BWP16P90CPD u_nand [DWIDTH-1:0] (
       .A1 (i_a),
       .A2 (i_b),
       .ZN (o_z)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_nand[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   NAND2_X4N_A7P5PP84TR_C16 u_nand [DWIDTH-1:0] (
       .A (i_a),
       .B (i_b),
       .Y (o_z)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_nand[*]] .preserve true
   //cadence script_end
`else
   // Delay required for behavioral PDE
   assign #(PS_DLY*1ps) o_z = ~(i_a & i_b);
`endif

endmodule

module ddr_and #(
   parameter DWIDTH = 1
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

`ifdef DDR_SLIB_TSMC12FFC
   CKAN2D1BWP16P90CPD u_and [DWIDTH-1:0] (
       .A1 (i_a),
       .A2 (i_b),
       .Z  (o_z)
   );
   //cadence script_begin
   //set_db -quiet [get_db insts */u_and[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   AND2_X2N_A7P5PP84TR_C16 u_and [DWIDTH-1:0] (
       .A (i_a),
       .B (i_b),
       .Y (o_z)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_and[*]] .preserve true
   //cadence script_end
`else
   assign o_z = i_a & i_b;
`endif

endmodule

module ddr_nor #(
   parameter DWIDTH = 1
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

`ifdef DDR_SLIB_TSMC12FFC
   CKNR2D1BWP16P90CPD u_nor [DWIDTH-1:0] (
      .A1 (i_a),
      .A2 (i_b),
      .ZN (o_z)
   );
   //cadence script_begin
   //set_db -quiet [get_db insts */u_nor[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   NOR2_X4N_A7P5PP84TR_C16 u_nor [DWIDTH-1:0] (
       .A (i_a),
       .B (i_b),
       .Y (o_z)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_nor[*]] .preserve true
   //cadence script_end
`else
   assign o_z = ~(i_a | i_b);
`endif

endmodule

module ddr_or #(
   parameter DWIDTH = 1
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

`ifdef DDR_SLIB_TSMC12FFC
   CKOR2D1BWP16P90CPD u_or [DWIDTH-1:0] (
      .A1 (i_a),
      .A2 (i_b),
      .Z  (o_z)
   );
   //cadence script_begin
   //set_db -quiet [get_db insts */u_or[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   OR2_X2N_A7P5PP84TR_C16 u_or [DWIDTH-1:0] (
       .A (i_a),
       .B (i_b),
       .Y (o_z)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_or[*]] .preserve true
   //cadence script_end
`else
   assign o_z = i_a | i_b;
`endif

endmodule

//// Tristate buffer
//module ddr_buft #(
//   parameter DWIDTH = 1
//) (
//   input  logic [DWIDTH-1:0] i_a,
//   input  logic [DWIDTH-1:0] i_en,
//   output logic [DWIDTH-1:0] o_z
//);
//
//`ifdef DDR_SLIB_TSMC12FFC
//   BUFTD8BWP16P90CPD u_buft [DWIDTH-1:0] (
//      .I  (i_a),
//      .OE (i_en),
//      .Z  (o_z)
//   );
//   //cadence script_begin
//   //set_db -quiet [get_db insts */u_buft[*]] .preserve true
//   //cadence script_end
//`else
//   assign o_z = i_en ? i_a : 'bz;
//`endif
//
//endmodule

module ddr_xor #(
   parameter DWIDTH = 1
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

`ifdef DDR_SLIB_TSMC12FFC
   CKXOR2D1BWP16P90CPD u_xor [DWIDTH-1:0] (
      .A1 (i_a),
      .A2 (i_b),
      .Z  (o_z)
   );
   //cadence script_begin
   //set_db -quiet [get_db insts */u_xor[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   XOR2_X4N_A7P5PP84TR_C16 u_xor [DWIDTH-1:0] (
       .A (i_a),
       .B (i_b),
       .Y (o_z)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_xor[*]] .preserve true
   //cadence script_end
`else
   assign o_z = (i_a ^ i_b);
`endif
endmodule

module ddr_xnor #(
   parameter DWIDTH = 1
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

`ifdef DDR_SLIB_TSMC12FFC
   XNR2D0BWP16P90CPD u_xnor [DWIDTH-1:0] (
      .A1 (i_a),
      .A2 (i_b),
      .ZN (o_z)
   );
   //cadence script_begin
   //set_db -quiet [get_db insts */u_xnor[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   XNOR2_X4N_A7P5PP84TR_C16 u_xnor [DWIDTH-1:0] (
       .A (i_a),
       .B (i_b),
       .Y (o_z)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_xnor[*]] .preserve true
   //cadence script_end
`else
   assign o_z = ~(i_a ^ i_b);
`endif

endmodule

module ddr_nand3 #(
   parameter DWIDTH = 1
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   input  logic [DWIDTH-1:0] i_c,
   output logic [DWIDTH-1:0] o_z
);

`ifdef DDR_SLIB_TSMC12FFC
   ND3D0BWP16P90CPD u_nand3 [DWIDTH-1:0] (
      .A1 (i_a),
      .A2 (i_b),
      .A3 (i_c),
      .ZN (o_z)
   );
   //cadence script_begin
   //set_db -quiet [get_db insts */u_nand3[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   NAND3_X4N_A7P5PP84TR_C16 u_nand3 [DWIDTH-1:0] (
       .A (i_a),
       .B (i_b),
       .C (i_c),
       .Y (o_z)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_nand3[*]] .preserve true
   //cadence script_end
`else
   assign o_z = ~(i_a & i_b & i_c);
`endif

endmodule

module ddr_and3 #(
   parameter DWIDTH = 1
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   input  logic [DWIDTH-1:0] i_c,
   output logic [DWIDTH-1:0] o_z
);

`ifdef DDR_SLIB_TSMC12FFC
   AN3D0BWP16P90CPD u_and3 [DWIDTH-1:0] (
      .A1 (i_a),
      .A2 (i_b),
      .A3 (i_c),
      .Z  (o_z)
   );
   //cadence script_begin
   //set_db -quiet [get_db insts */u_and3[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   AND3_X2N_A7P5PP84TR_C16 u_and3 [DWIDTH-1:0] (
       .A (i_a),
       .B (i_b),
       .C (i_c),
       .Y (o_z)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_and3[*]] .preserve true
   //cadence script_end
`else
   assign o_z = (i_a & i_b & i_c);
`endif
endmodule

module ddr_nand4 #(
   parameter DWIDTH = 1
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   input  logic [DWIDTH-1:0] i_c,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_z
);

`ifdef DDR_SLIB_TSMC12FFC
   ND4D0BWP16P90CPD u_nand4 [DWIDTH-1:0] (
      .A1 (i_a),
      .A2 (i_b),
      .A3 (i_c),
      .A4 (i_d),
      .ZN (o_z)
   );
   //cadence script_begin
   //set_db -quiet [get_db insts */u_nand4[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   NAND4_X4N_A7P5PP84TR_C16 u_nand4 [DWIDTH-1:0] (
       .A (i_a),
       .B (i_b),
       .C (i_c),
       .D (i_d),
       .Y (o_z)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_nand4[*]] .preserve true
   //cadence script_end
`else
   assign o_z = ~(i_a & i_b & i_c & i_d);
`endif

endmodule

// Reset Low CGC
module mc_cgc_rl (
   input  logic i_cgc_en,
   input  logic i_clk_en,
   input  logic i_clk,
   output logic o_clk
);

`ifdef DDR_SLIB_TSMC12FFC
   CKLNQD10BWP16P90CPD u_cgc (
      .CP (i_clk),
      .E  (i_clk_en),
      .TE (i_cgc_en),
      .Q  (o_clk)
   );
   //cadence script_begin
   //set_db -quiet [get_db insts */u_cgc] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   PREICG_X4N_A9PP84TL_C14 u_cgc (
       .CK  (i_clk),
       .E   (i_clk_en),
       .SE  (i_cgc_en),
       .ECK (o_clk)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_cgc] .preserve true
   //cadence script_end
`else
   logic clk_en, inv_clk, clk_test_en;

   ddr_or    u_or    (.i_a(i_clk_en), .i_b(i_cgc_en), .o_z(clk_test_en));
   ddr_inv   u_inv   (.i_a(i_clk), .o_z(inv_clk));
   ddr_latch u_latch (.i_clk(inv_clk), .i_d(clk_test_en), .o_q(clk_en));
   ddr_and   u_and   (.i_a(i_clk), .i_b(clk_en), .o_z(o_clk));
`endif

endmodule

module ddr_cgc_rl (
   input  logic i_cgc_en,
   input  logic i_clk_en,
   input  logic i_clk,
   output logic o_clk
);

`ifdef DDR_SLIB_TSMC12FFC
   CKLNQD10BWP16P90CPD u_cgc (
      .CP (i_clk),
      .E  (i_clk_en),
      .TE (i_cgc_en),
      .Q  (o_clk)
   );
   //cadence script_begin
   //set_db -quiet [get_db insts */u_cgc] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   PREICG_X4N_A7P5PP84TR_C16 u_cgc (
       .CK  (i_clk),
       .E   (i_clk_en),
       .SE  (i_cgc_en),
       .ECK (o_clk)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_cgc] .preserve true
   //cadence script_end
`else
   logic clk_en, inv_clk, clk_test_en;

   ddr_or    u_or    (.i_a(i_clk_en), .i_b(i_cgc_en), .o_z(clk_test_en));
   ddr_inv   u_inv   (.i_a(i_clk), .o_z(inv_clk));
   ddr_latch u_latch (.i_clk(inv_clk), .i_d(clk_test_en), .o_q(clk_en));
   ddr_and   u_and   (.i_a(i_clk), .i_b(clk_en), .o_z(o_clk));
`endif

endmodule

// Reset High CGC
module ddr_cgc_rh (
   input  logic i_cgc_en,
   input  logic i_clk_en,
   input  logic i_clk,
   output logic o_clk
);

`ifdef DDR_SLIB_TSMC12FFC
   CKLHQD10BWP16P90CPD u_cgc (
      .CPN(i_clk),
      .E  (i_clk_en),
      .TE (i_cgc_en),
      .Q  (o_clk)
   );
   //cadence script_begin
   //set_db -quiet [get_db insts */u_cgc] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   PREICGN_X4N_A7P5PP84TR_C16 u_cgc (
       .CK  (i_clk),
       .E   (i_clk_en),
       .SE  (i_cgc_en),
       .ECK (o_clk)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_cgc] .preserve true
   //cadence script_end
`else

   logic clk_en, clk_en_n, clk_test_en;

   ddr_or    u_or_0  (.i_a(i_clk_en), .i_b(i_cgc_en), .o_z(clk_test_en));
   ddr_latch u_latch (.i_clk(i_clk), .i_d(clk_test_en), .o_q(clk_en));
   ddr_inv   u_inv_0 (.i_a(clk_en), .o_z(clk_en_n));
   ddr_or    u_or_1  (.i_a(i_clk), .i_b(clk_en_n), .o_z(o_clk));
`endif

endmodule

module ddr_demet #(
   parameter DWIDTH = 1
) (
   input  logic              i_clk,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifdef DDR_SLIB_TSMC12FFC
   logic [DWIDTH-1:0] q0;
   SDFSYNQD1BWP16P90CPD u_sync_0 [DWIDTH-1:0] (
      .D  (i_d),
      .SI ('0),    //FIXME
      .SE ('0),    //FIXME
      .CP (i_clk),
      .Q  (q0)
   );

   SDFSYNQD1BWP16P90CPD u_sync_1 [DWIDTH-1:0] (
      .D  (q0),
      .SI ('0),    //FIXME
      .SE ('0),    //FIXME
      .CP (i_clk),
      .Q  (o_q)
   );

   //cadence script_begin
   //set_db -quiet [get_db insts */u_sync_*[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   SDFFYQ2D_X4N_A7P5PP84TR_C16 u_sync [DWIDTH-1:0] (
      .D  (i_d),
      .SI ('0),    //FIXME
      .SE ('0),    //FIXME
      .CK (i_clk),
      .Q  (o_q)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_sync[*]] .preserve true
   //cadence script_end
`else
   logic [DWIDTH-1:0] q0;
   ddr_dff u_dff_0 [DWIDTH-1:0] (.i_clk(i_clk), .i_d(i_d), .o_q(q0));
   ddr_dff u_dff_1 [DWIDTH-1:0] (.i_clk(i_clk), .i_d(q0), .o_q(o_q));
`endif

endmodule

module ddr_demet_r #(
   parameter DWIDTH = 1
) (
   input  logic              i_clk,
   input  logic              i_rst,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifdef DDR_SLIB_TSMC12FFC
   logic [DWIDTH-1:0] q0;
   logic rst_n;
   ddr_inv u_inv (.i_a(i_rst), .o_z(rst_n));

   SDFSYNCNQD1BWP16P90CPD u_sync_0 [DWIDTH-1:0] (
      .D   (i_d),
      .SI  ('0),
      .SE  ('0),
      .CDN (rst_n),
      .CP  (i_clk),
      .Q   (q0)
   );

   SDFSYNCNQD1BWP16P90CPD u_sync_1 [DWIDTH-1:0] (
      .D   (q0),
      .SI  ('0),
      .SE  ('0),
      .CDN (rst_n),
      .CP  (i_clk),
      .Q   (o_q)
   );

   //cadence script_begin
   //set_db -quiet [get_db insts */u_sync_*[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   SDFFYRPQ2D_X4N_A7P5PP84TR_C16 u_sync [DWIDTH-1:0] (
      .R  (i_rst),
      .D  (i_d),
      .SI ('0),    //FIXME
      .SE ('0),    //FIXME
      .CK (i_clk),
      .Q  (o_q)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_sync[*]] .preserve true
   //cadence script_end
`else
   logic [DWIDTH-1:0] q0;
   ddr_dff_r u_dff_0 [DWIDTH-1:0] (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_d), .o_q(q0));
   ddr_dff_r u_dff_1 [DWIDTH-1:0] (.i_clk(i_clk), .i_rst(i_rst), .i_d(q0), .o_q(o_q));
`endif

endmodule

module ddr_demet_s #(
   parameter DWIDTH = 1
) (
   input  logic              i_clk,
   input  logic              i_set,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifdef DDR_SLIB_TSMC12FFC
   logic [DWIDTH-1:0] q0;
   logic set_n;
   ddr_inv u_inv (.i_a(i_set), .o_z(set_n));

   SDFSYNSNQD1BWP16P90CPD u_sync_0 [DWIDTH-1:0] (
      .D   (i_d),
      .SI  ('0),
      .SE  ('0),
      .SDN (set_n),
      .CP  (i_clk),
      .Q   (q0)
   );

   SDFSYNSNQD1BWP16P90CPD u_sync_1 [DWIDTH-1:0] (
      .D   (q0),
      .SI  ('0),
      .SE  ('0),
      .SDN (set_n),
      .CP  (i_clk),
      .Q   (o_q)
   );

   //cadence script_begin
   //set_db -quiet [get_db insts */u_sync_*[*]] .preserve true
   //cadence script_end
`elsif DDR_SLIB_GF12LPP
   logic set_n;
   ddr_inv u_inv (.i_a(i_set), .o_z(set_n));

   SDFFYSQ2D_X4N_A7P5PP84TR_C16 u_sync [DWIDTH-1:0] (
      .SN  (set_n),
      .D  (i_d),
      .SI ('0),    //FIXME
      .SE ('0),    //FIXME
      .CK (i_clk),
      .Q  (o_q)
    ) ;

   //cadence script_begin
   //set_db -quiet [get_db insts */u_sync[*]] .preserve true
   //cadence script_end
`else
   logic [DWIDTH-1:0] q0;
   ddr_dff_s u_dff_0 [DWIDTH-1:0] (.i_clk(i_clk), .i_set(i_set), .i_d(i_d), .o_q(q0 ));
   ddr_dff_s u_dff_1 [DWIDTH-1:0] (.i_clk(i_clk), .i_set(i_set), .i_d(q0 ), .o_q(o_q));
`endif

endmodule
