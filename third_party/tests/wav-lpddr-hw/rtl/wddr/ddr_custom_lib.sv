
/*********************************************************************************
Copyright (c) 2021 Wavious LLC

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

*********************************************************************************/

`include "ddr_global_define.vh"
`include "ddr_project_define.vh"

import ddr_global_pkg::*;

module ddr_wcm_inv #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_a,
   output logic [DWIDTH-1:0] o_z
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`endif

`ifdef DDR_CLIB
   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      INV_D2_GL16_LVT u_inv [DWIDTH-1:0](
   `elsif DDR_CLIB_WAV8LPU
      INV_D2_GL20_LVT u_inv [DWIDTH-1:0](
   `elsif DDR_CLIB_WAV12LPP
      INV_D2_GL16_LVT u_inv [DWIDTH-1:0](
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .in   (i_a),
         .out  (o_z)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      INV_D2_GL16_SVT u_inv [DWIDTH-1:0](
   `elsif DDR_CLIB_WAV8LPU
      INV_D2_GL20_SVT u_inv [DWIDTH-1:0](
   `elsif DDR_CLIB_WAV12LPP
      INV_D2_GL16_RVT u_inv [DWIDTH-1:0](
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .in   (i_a),
         .out  (o_z)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_inv[*]] .preserve true
   //cadence script_end
`else
   assign o_z = ~i_a;
`endif

endmodule

module ddr_wcm_invx8 #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_a,
   output logic [DWIDTH-1:0] o_z
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`endif

`ifdef DDR_CLIB
   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      INV_D8_GL16_LVT u_inv [DWIDTH-1:0](
   `elsif DDR_CLIB_WAV8LPU
      INV_D8_GL20_LVT u_inv [DWIDTH-1:0](
   `elsif DDR_CLIB_WAV12LPP
      INV_D8_GL16_LVT u_inv [DWIDTH-1:0](
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .in   (i_a),
         .out  (o_z)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      INV_D8_GL16_SVT u_inv [DWIDTH-1:0](
   `elsif DDR_CLIB_WAV8LPU
      INV_D8_GL20_SVT u_inv [DWIDTH-1:0](
   `elsif DDR_CLIB_WAV12LPP
      INV_D8_GL16_RVT u_inv [DWIDTH-1:0](
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .in   (i_a),
         .out  (o_z)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_inv[*]] .preserve true
   //cadence script_end
`else
   assign o_z = ~i_a;
`endif

endmodule

module ddr_wcm_bufx8 #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_a,
   output logic [DWIDTH-1:0] o_z
);

   logic [DWIDTH-1:0] z_b;

   ddr_wcm_inv #(
      .DWIDTH (DWIDTH),
      .LVT    (LVT)
   ) u_inv (
      .i_a (i_a),
      .o_z (z_b)
   );

   ddr_wcm_invx8 #(
      .DWIDTH (DWIDTH),
      .LVT    (LVT)
   ) u_inv_d8 (
      .i_a (z_b),
      .o_z (o_z)
   );

endmodule

module ddr_wcm_nmux #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic              i_sel,
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z_b
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`endif

`ifdef DDR_CLIB
   logic sel_b;

   ddr_wcm_inv #(
      .LVT (LVT)
   ) u_inv (
      .i_a (i_sel),
      .o_z (sel_b)
   );

   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      MUXT2_D2_GL16_LVT u_mux [DWIDTH-1:0](
   `elsif DDR_CLIB_WAV8LPU
      MUXT2_D2_GL20_LVT u_mux [DWIDTH-1:0](
   `elsif DDR_CLIB_WAV12LPP
      MUXT2_D2_GL16_LVT u_mux [DWIDTH-1:0](
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .a   (i_a),
         .b   (i_b),
         .s   (i_sel),
         .sb  (sel_b),
         .yb  (o_z_b)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      MUXT2_D2_GL16_SVT u_mux [DWIDTH-1:0](
   `elsif DDR_CLIB_WAV8LPU
      MUXT2_D2_GL20_SVT u_mux [DWIDTH-1:0](
   `elsif DDR_CLIB_WAV12LPP
      MUXT2_D2_GL16_RVT u_mux [DWIDTH-1:0](
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .a   (i_a),
         .b   (i_b),
         .s   (i_sel),
         .sb  (sel_b),
         .yb  (o_z_b)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_mux[*]] .preserve true
   //cadence script_end
`else
   assign o_z_b = ~(i_sel ? i_b : i_a);
`endif

endmodule

module ddr_wcm_mux #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic              i_sel,
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

   logic [DWIDTH-1:0] z_b;

   ddr_wcm_nmux #(
      .DWIDTH (DWIDTH),
      .LVT    (LVT)
   ) u_nmux (
      .i_sel  (i_sel),
      .i_a    (i_a),
      .i_b    (i_b),
      .o_z_b  (z_b)
   );

   ddr_wcm_inv #(
      .DWIDTH (DWIDTH),
      .LVT    (LVT)
   ) u_inv (
      .i_a (z_b),
      .o_z (o_z)
   );

endmodule

module ddr_wcm_latch_s #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic              i_clk,
   input  logic              i_clk_b,
   input  logic              i_set,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`endif

`ifdef DDR_CLIB

   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      LATSET_D1_GL16_LVT u_latch [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      LATSET_D1_GL20_LVT u_latch [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      LATSET_D1_GL16_LVT u_latch [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd  (vdd),
         .vss  (vss),
      `endif
         .q    (o_q),
         .clk  (i_clk),
         .clkb (i_clk_b),
         .d    (i_d),
         .set  (i_set)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      LATSET_D1_GL16_SVT u_latch [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      LATSET_D1_GL20_SVT u_latch [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      LATSET_D1_GL16_RVT u_latch [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd  (vdd),
         .vss  (vss),
      `endif
         .q    (o_q),
         .clk  (i_clk),
         .clkb (i_clk_b),
         .d    (i_d),
         .set  (i_set)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_latch[*]] .preserve true
   //cadence script_end
`else
   always_latch
     if (i_set)
        o_q <= '1;
     else if (i_clk)
        o_q <= i_d;
`endif

endmodule

module ddr_wcm_latch_r #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic              i_clk,
   input  logic              i_clk_b,
   input  logic              i_rst,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`endif

`ifdef DDR_CLIB_WAV
   logic rst_b;

   ddr_wcm_inv #(
      .LVT    (LVT)
   ) u_inv (
      .i_a    (i_rst),
      .o_z    (rst_b)
   );

   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      LATRES_D1_GL16_LVT u_latch [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      LATRES_D1_GL20_LVT u_latch [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      LATRES_D1_GL16_LVT u_latch [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd  (vdd),
         .vss  (vss),
      `endif
         .q    (o_q),
         .clk  (i_clk),
         .clkb (i_clk_b),
         .d    (i_d),
         .rstb (rst_b)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      LATRES_D1_GL16_SVT u_latch [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      LATRES_D1_GL20_SVT u_latch [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      LATRES_D1_GL16_RVT u_latch [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd  (vdd),
         .vss  (vss),
      `endif
         .q    (o_q),
         .clk  (i_clk),
         .clkb (i_clk_b),
         .d    (i_d),
         .rstb (rst_b)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_latch[*]] .preserve true
   //cadence script_end
`else
   always_latch
     if (i_rst)
        o_q <= '0;
     else if (i_clk)
        o_q <= i_d;
`endif

endmodule

module ddr_wcm_latch #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic              i_clk,
   input  logic              i_clk_b,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`endif

`ifdef DDR_CLIB

   if (LVT) begin : LVTH

   `ifdef DDR_CLIB_WAV12FFC
      LAT_D1_GL16_LVT u_latch [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      LAT_D1_GL20_LVT u_latch [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      LAT_D1_GL16_LVT u_latch [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd  (vdd),
         .vss  (vss),
      `endif
         .q    (o_q),
         .clk  (i_clk),
         .clkb (i_clk_b),
         .d    (i_d)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      LAT_D1_GL16_SVT u_latch [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      LAT_D1_GL20_SVT u_latch [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      LAT_D1_GL16_RVT u_latch [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd  (vdd),
         .vss  (vss),
      `endif
         .q    (o_q),
         .clk  (i_clk),
         .clkb (i_clk_b),
         .d    (i_d)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_latch[*]] .preserve true
   //cadence script_end
`else
   always_latch
     if (i_clk)
        o_q <= i_d;
`endif

endmodule

module ddr_wcm_dff #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic              i_clk,
   input  logic              i_clk_b,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`else
 `ifndef WLOGIC_NO_TIE
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
 `endif
`endif

`ifdef DDR_CLIB

   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      FF_D1_GL16_LVT u_ff [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      FF_D1_GL20_LVT u_ff [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      FF_D1_GL16_LVT u_ff [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd  (vdd),
         .vss  (vss),
      `endif
         .q    (o_q),
         .clk  (i_clk),
         .clkb (i_clk_b),
         .d    (i_d)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      FF_D1_GL16_SVT u_ff [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      FF_D1_GL20_SVT u_ff [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      FF_D1_GL16_RVT u_ff [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_TIE
         .tiehi (vdd),
         .tielo (vss),
      `endif
      `ifndef WLOGIC_NO_PG
         .vdd  (vdd),
         .vss  (vss),
      `endif
         .q    (o_q),
         .clk  (i_clk),
         .clkb (i_clk_b),
         .d    (i_d)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_ff[*]] .preserve true
   //cadence script_end
`else
   always_ff @ (posedge i_clk)
      o_q <= i_d;
`endif

endmodule

module ddr_wcm_dff_r #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic              i_clk,
   input  logic              i_clk_b,
   input  logic              i_rst,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`else
 `ifndef WLOGIC_NO_TIE
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
 `endif
`endif

`ifdef DDR_CLIB
   logic rst_b;

   ddr_wcm_inv #(
      .LVT    (LVT)
   ) u_inv (
      .i_a    (i_rst),
      .o_z    (rst_b)
   );

   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      FFRES_D1_GL16_LVT u_ff [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      FFRES_D1_GL20_LVT u_ff [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      FFRES_D1_GL16_LVT u_ff [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd  (vdd),
         .vss  (vss),
      `endif
         .q    (o_q),
         .clk  (i_clk),
         .nlkb (i_clk_b),
         .rst  (i_rst),
         .rstb (rst_b),
         .d    (i_d)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      FFRES_D1_GL16_SVT u_ff [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      FFRES_D1_GL20_SVT u_ff [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      FFRES_D1_GL16_RVT u_ff [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_TIE
         .tiehi (vdd),
         .tielo (vss),
      `endif
      `ifndef WLOGIC_NO_PG
         .vdd  (vdd),
         .vss  (vss),
      `endif
         .q    (o_q),
         .clk  (i_clk),
         .clkb (i_clk_b),
         .rst  (i_rst),
         .rstb (rst_b),
         .d    (i_d)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_ff[*]] .preserve true
   //cadence script_end
`else
   always_ff @(posedge i_clk, posedge i_rst)
      if (i_rst)
         o_q <= '0;
      else
         o_q <= i_d;
`endif

endmodule

module ddr_wcm_nand #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`else
 `ifndef WLOGIC_NO_TIE
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
 `endif
`endif

`ifdef DDR_CLIB
   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      NAND2_D1_GL16_LVT u_nand [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      NAND2_D1_GL20_LVT u_nand [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      NAND2_D1_GL16_LVT u_nand [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .a  (i_a),
         .b  (i_b),
         .y  (o_z)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      NAND2_D1_GL16_SVT u_nand [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      NAND2_D1_GL20_SVT u_nand [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      NAND2_D1_GL16_RVT u_nand [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_TIE
         .tiehi (vdd),
         .tielo (vss),
      `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .a  (i_a),
         .b  (i_b),
         .y  (o_z)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_nand[*]] .preserve true
   //cadence script_end
`else
   assign o_z = ~(i_a & i_b);
`endif

endmodule

module ddr_wcm_and #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

   logic [DWIDTH-1:0] z_b;
   ddr_wcm_nand #(.DWIDTH(DWIDTH),.LVT(LVT)) u_nand (.i_a(i_a), .i_b(i_b), .o_z(z_b));
   ddr_wcm_inv  #(.DWIDTH(DWIDTH),.LVT(LVT)) u_inv (.i_a(z_b), .o_z(o_z));

endmodule

module ddr_wcm_nor #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`else
 `ifndef WLOGIC_NO_TIE
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
 `endif
`endif

`ifdef DDR_CLIB
   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      NOR2_D1_GL16_LVT u_nor [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      NOR2_D1_GL20_LVT u_nor [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      NOR2_D1_GL16_LVT u_nor [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .a  (i_a),
         .b  (i_b),
         .y  (o_z)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      NOR2_D1_GL16_SVT u_nor [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      NOR2_D1_GL20_SVT u_nor [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      NOR2_D1_GL16_RVT u_nor [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_TIE
         .tiehi (vdd),
         .tielo (vss),
      `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .a  (i_a),
         .b  (i_b),
         .y  (o_z)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_nor[*]] .preserve true
   //cadence script_end
`else
   assign o_z = ~(i_a | i_b);
`endif

endmodule

module ddr_wcm_or #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

   logic [DWIDTH-1:0] z_b;
   ddr_wcm_nor #(.DWIDTH(DWIDTH),.LVT(LVT)) u_nor (.i_a(i_a), .i_b(i_b), .o_z(z_b));
   ddr_wcm_inv #(.DWIDTH(DWIDTH),.LVT(LVT)) u_inv (.i_a(z_b), .o_z(o_z));

endmodule

module ddr_wcm_invt #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_en,
   input  logic [DWIDTH-1:0] i_a,
   output logic [DWIDTH-1:0] o_z
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`endif

   logic [DWIDTH-1:0] en_b;

   ddr_wcm_inv #(.DWIDTH(DWIDTH),.LVT(LVT)) u_inv (.i_a(i_en), .o_z(en_b));

`ifdef DDR_CLIB
   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      INVT_D2_GL16_LVT u_invt [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      INVT_D2_GL20_LVT u_invt [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      INVT_D2_GL16_LVT u_invt [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .en   (i_en),
         .enb  (en_b),
         .in   (i_a),
         .out  (o_z)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      INVT_D2_GL16_SVT u_invt [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      INVT_D2_GL20_SVT u_invt [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      INVT_D2_GL16_RVT u_invt [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .en   (i_en),
         .enb  (en_b),
         .in   (i_a),
         .out  (o_z)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_invt[*]] .preserve true
   //cadence script_end
`else
   assign o_z = i_en ? ~i_a : 'bz;
`endif

endmodule

module ddr_wcm_buft #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_en,
   output logic [DWIDTH-1:0] o_z
);

   logic [DWIDTH-1:0] z_b;
   ddr_wcm_inv  #(.DWIDTH(DWIDTH),.LVT(LVT)) u_inv  (.i_a(i_a), .o_z(z_b));
   ddr_wcm_invt #(.DWIDTH(DWIDTH),.LVT(LVT)) u_invt (.i_a(z_b), .i_en(i_en), .o_z(o_z));

endmodule

module ddr_wcm_buf #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_a,
   output logic [DWIDTH-1:0] o_z
);

   logic [DWIDTH-1:0] z_b;
   ddr_wcm_inv #(.DWIDTH(DWIDTH),.LVT(LVT)) u_inv_0 (.i_a(i_a), .o_z(z_b));
   ddr_wcm_inv #(.DWIDTH(DWIDTH),.LVT(LVT)) u_inv_1 (.i_a(z_b), .o_z(o_z));

endmodule

module ddr_wcm_xor #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`endif

`ifdef DDR_CLIB
   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      XOR_D2_GL16_LVT u_xor [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      XOR_D2_GL20_LVT u_xor [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      XOR_D2_GL16_LVT u_xor [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .a  (i_a),
         .b  (i_b),
         .out(o_z)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      XOR_D2_GL16_SVT u_xor [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      XOR_D2_GL20_SVT u_xor [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      XOR_D2_GL16_RVT u_xor [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .a  (i_a),
         .b  (i_b),
         .out(o_z)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_xor[*]] .preserve true
   //cadence script_end
`else
   assign o_z = i_a ^ i_b;
`endif

endmodule

module ddr_wcm_xnor #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

   logic [DWIDTH-1:0] z_b;
   ddr_wcm_xor #(.DWIDTH(DWIDTH),.LVT(LVT)) u_xor (.i_a(i_a), .i_b(i_b), .o_z(z_b));
   ddr_wcm_inv #(.DWIDTH(DWIDTH),.LVT(LVT)) u_inv (.i_a(z_b), .o_z(o_z));

endmodule

module ddr_wcm_nand3 #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   input  logic [DWIDTH-1:0] i_c,
   output logic [DWIDTH-1:0] o_z
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`else
 `ifndef WLOGIC_NO_TIE
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
 `endif
`endif

`ifdef DDR_CLIB
   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      NAND3_D1_GL16_LVT u_nand3 [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      NAND3_D1_GL20_LVT u_nand3 [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      NAND3_D1_GL16_LVT u_nand3 [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .a  (i_a),
         .b  (i_b),
         .c  (i_c),
         .y  (o_z)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      NAND3_D1_GL16_SVT u_nand3 [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      NAND3_D1_GL20_SVT u_nand3 [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      NAND3_D1_GL16_RVT u_nand3 [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_TIE
         .tiehi (vdd),
         .tielo (vss),
      `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .a  (i_a),
         .b  (i_b),
         .c  (i_c),
         .y  (o_z)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_nand3[*]] .preserve true
   //cadence script_end
`else
   assign o_z = ~(i_a & i_b & i_c);
`endif

endmodule

module ddr_wcm_and3 #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   input  logic [DWIDTH-1:0] i_c,
   output logic [DWIDTH-1:0] o_z
);

   logic [DWIDTH-1:0] z_b;
   ddr_wcm_nand3 #(.DWIDTH(DWIDTH),.LVT(LVT)) u_nand3 (.i_a(i_a), .i_b(i_b), .i_c(i_c), .o_z(z_b));
   ddr_wcm_inv   #(.DWIDTH(DWIDTH),.LVT(LVT)) u_inv   (.i_a(z_b), .o_z(o_z));

endmodule

module ddr_wcm_demet #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic              i_clk,
   input  logic              i_clk_b,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`else
 `ifndef WLOGIC_NO_TIE
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
 `endif
`endif

`ifdef DDR_CLIB
   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      FF_DEMET_D1_GL16_LVT u_demet [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      FF_DEMET_D1_GL20_LVT u_demet [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      FF_DEMET_D1_GL16_LVT u_demet [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .d    (i_d),
         .clk  (i_clk),
         .clkb (i_clk_b),
         .q    (o_q)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      FF_DEMET_D1_GL16_SVT u_demet [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      FF_DEMET_D1_GL20_SVT u_demet [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      FF_DEMET_D1_GL16_RVT u_demet [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_TIE
         .tiehi (vdd),
         .tielo (vss),
      `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .d    (i_d),
         .clk  (i_clk),
         .clkb (i_clk_b),
         .q    (o_q)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_demet[*]] .preserve true
   //cadence script_end
`else
   logic [DWIDTH-1:0] q0;
   ddr_wcm_dff #(.LVT(LVT)) u_dff_0 [DWIDTH-1:0] (.i_clk(i_clk), .i_clk_b(i_clk_b), .i_d(i_d), .o_q(q0 ));
   ddr_wcm_dff #(.LVT(LVT)) u_dff_1 [DWIDTH-1:0] (.i_clk(i_clk), .i_clk_b(i_clk_b), .i_d(q0 ), .o_q(o_q));
`endif

endmodule

module ddr_wcm_demet_r #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic              i_clk,
   input  logic              i_clk_b,
   input  logic              i_rst,
   input  logic [DWIDTH-1:0] i_d,
   output logic [DWIDTH-1:0] o_q
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`endif

`ifdef DDR_CLIB
   logic rst_b;

   ddr_wcm_inv #(
      .LVT    (LVT)
   ) u_inv (
      .i_a    (i_rst),
      .o_z    (rst_b)
   );

   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      FFRES_DEMET_D1_GL16_LVT u_demet [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      FFRES_DEMET_D1_GL20_LVT u_demet [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      FFRES_DEMET_D1_GL16_LVT u_demet [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .d    (i_d),
         .clk  (i_clk),
         .clkb (i_clk_b),
         .rst  (i_rst),
         .rstb (rst_b),
         .q    (o_q)
      );
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      FFRES_DEMET_D1_GL16_SVT u_demet [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV8LPU
      FFRES_DEMET_D1_GL20_SVT u_demet [DWIDTH-1:0] (
   `elsif DDR_CLIB_WAV12LPP
      FFRES_DEMET_D1_GL16_RVT u_demet [DWIDTH-1:0] (
   `endif
      `ifndef WLOGIC_NO_PG
         .vdd (vdd),
         .vss (vss),
      `endif
         .d    (i_d),
         .clk  (i_clk),
         .clkb (i_clk_b),
         .rst  (i_rst),
         .rstb (rst_b),
         .q    (o_q)
      );
   end

   //cadence script_begin
   //set_db [get_db insts *VTH.u_demet[*]] .preserve true
   //cadence script_end
`else
   logic [DWIDTH-1:0] q0;
   ddr_wcm_dff_r #(.LVT(LVT)) u_dff_0 [DWIDTH-1:0] (.i_clk(i_clk), .i_clk_b(i_clk_b), .i_rst(i_rst), .i_d(i_d), .o_q(q0));
   ddr_wcm_dff_r #(.LVT(LVT)) u_dff_1 [DWIDTH-1:0] (.i_clk(i_clk), .i_clk_b(i_clk_b), .i_rst(i_rst), .i_d(q0), .o_q(o_q));
`endif

endmodule

module ddr_wcm_mux_se #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic              i_sel,
   input  logic              i_en,
   input  logic [DWIDTH-1:0] i_a,
   input  logic [DWIDTH-1:0] i_b,
   output logic [DWIDTH-1:0] o_z
);

`ifdef DDR_CLIB
   if (LVT) begin : LVTH
      assign o_z = '0;     // FIXME
   end else begin : SVTH
      assign o_z = '0;     // FIXME
   end
`else
   assign o_z = i_en ? i_sel ? i_b : i_a : 'bz;
`endif

endmodule

module ddr_wcm_func_mux_4to1 #(
   parameter       DWIDTH = 1,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0] i_clk_0,
   input  logic [DWIDTH-1:0] i_clk_90,
   input  logic [DWIDTH-1:0] i_clk_180,
   input  logic [DWIDTH-1:0] i_clk_270,
   input  logic [DWIDTH-1:0] i_d0,
   input  logic [DWIDTH-1:0] i_d1,
   input  logic [DWIDTH-1:0] i_d2,
   input  logic [DWIDTH-1:0] i_d3,
   output wire  [DWIDTH-1:0] o_q
);

   logic [DWIDTH-1:0] l0, l1, l2, l3;
   wire  [DWIDTH-1:0] q;

`ifdef DDR_SER_4TO1_NEGEDGE
   // Parallel data launched on falling edge of clk_0
   ddr_wcm_latch #(.LVT(LVT)) u_latch_0 [DWIDTH-1:0] (.i_clk(i_clk_90 ), .i_clk_b(i_clk_270), .i_d(i_d0), .o_q(l0)); // Quarter cycle setup time to mux
   ddr_wcm_latch #(.LVT(LVT)) u_latch_1 [DWIDTH-1:0] (.i_clk(i_clk_180), .i_clk_b(i_clk_0  ), .i_d(i_d1), .o_q(l1)); // Quarter cycle setup time to mux
   ddr_wcm_latch #(.LVT(LVT)) u_latch_2 [DWIDTH-1:0] (.i_clk(i_clk_270), .i_clk_b(i_clk_90 ), .i_d(i_d2), .o_q(l2)); // Quarter cycle setup time to mux
   ddr_wcm_latch #(.LVT(LVT)) u_latch_3 [DWIDTH-1:0] (.i_clk(i_clk_0  ), .i_clk_b(i_clk_180), .i_d(i_d3), .o_q(l3)); // Quarter cycle setup time to mux

   // Wire-OR'd mux output
   ddr_wcm_mux_se #(.LVT(LVT)) u_mux_se_0 [DWIDTH-1:0] (.i_sel(i_clk_270), .i_en(i_clk_180), .i_a(l0), .i_b(l1), .o_z(q));
   ddr_wcm_mux_se #(.LVT(LVT)) u_mux_se_1 [DWIDTH-1:0] (.i_sel(i_clk_90 ), .i_en(i_clk_0  ), .i_a(l2), .i_b(l3), .o_z(q));

`else // POSEDGE
   // Parallel data launched on rising edge of clk_0
   ddr_wcm_latch #(.LVT(LVT)) u_latch_0 [DWIDTH-1:0] (.i_clk(i_clk_270), .i_clk_b(i_clk_90 ), .i_d(i_d0), .o_q(l0)); // Quarter cycle setup time to mux
   ddr_wcm_latch #(.LVT(LVT)) u_latch_1 [DWIDTH-1:0] (.i_clk(i_clk_0  ), .i_clk_b(i_clk_180), .i_d(i_d1), .o_q(l1)); // Quarter cycle setup time to mux
   ddr_wcm_latch #(.LVT(LVT)) u_latch_2 [DWIDTH-1:0] (.i_clk(i_clk_90 ), .i_clk_b(i_clk_270), .i_d(i_d2), .o_q(l2)); // Quarter cycle setup time to mux
   ddr_wcm_latch #(.LVT(LVT)) u_latch_3 [DWIDTH-1:0] (.i_clk(i_clk_180), .i_clk_b(i_clk_0  ), .i_d(i_d3), .o_q(l3)); // Quarter cycle setup time to mux

   // Wire-OR'd mux output
   ddr_wcm_mux_se #(.LVT(LVT)) u_mux_se_1 [DWIDTH-1:0] (.i_sel(i_clk_90 ), .i_en(i_clk_0  ), .i_a(l0), .i_b(l1), .o_z(q));
   ddr_wcm_mux_se #(.LVT(LVT)) u_mux_se_0 [DWIDTH-1:0] (.i_sel(i_clk_270), .i_en(i_clk_180), .i_a(l2), .i_b(l3), .o_z(q));

`endif // DDR_SER_4TO1_NEGEDGE

   assign o_q = q;

endmodule

module ddr_wcm_div2_2ph #(
   parameter [0:0] LVT= 1'b0
) (
   input  logic i_clk_0,
   input  logic i_clk_180,
   input  logic i_div_en,
   input  logic i_div_byp,
   output logic o_clk_0,
   output logic o_clk_180
);

   logic rst;
   ddr_wcm_inv #(.LVT(LVT)) u_inv_0 (.i_a(i_div_en), .o_z(rst));

`ifndef WLOGIC_NO_PG
   wire vdda, vss;
   assign vdda = 1'b1;
   assign vss  = 1'b0;
`endif

   if (LVT) begin : LVTH
     wphy_clk_div_2ph_4g_lvt u_clk_div_2ph (
   `ifndef WLOGIC_NO_PG
      .vdda           (vdda),
      .vss            (vss),
   `endif
      .i_rst          (rst),
      .i_byp          (i_div_byp),
      .i_clk0         (i_clk_0),
      .i_clk180       (i_clk_180),
      .o_clk0         (o_clk_0),
      .o_clk180       (o_clk_180)
   );

   end else begin : SVTH
     wphy_clk_div_2ph_4g_svt u_clk_div_2ph (
   `ifndef WLOGIC_NO_PG
      .vdda           (vdda),
      .vss            (vss),
   `endif
      .i_rst          (rst),
      .i_byp          (i_div_byp),
      .i_clk0         (i_clk_0),
      .i_clk180       (i_clk_180),
      .o_clk0         (o_clk_0),
      .o_clk180       (o_clk_180)
   );

   end

endmodule

// 4PH clock divider used in DP
module ddr_wcm_div2_4ph #(
   parameter [0:0] LVT= 1'b0
) (
   input  logic i_clk_0,
   input  logic i_clk_90,
   input  logic i_clk_180,
   input  logic i_clk_270,
   input  logic i_div_en,
   input  logic i_div_byp,
   output logic o_clk_0,
   output logic o_clk_90,
   output logic o_clk_180,
   output logic o_clk_270
);

   logic rst;
   ddr_wcm_inv #(.LVT(LVT)) u_inv_0 (.i_a(i_div_en), .o_z(rst));

`ifndef WLOGIC_NO_PG
   wire vdda, vss;
   assign vdda = 1'b1;
   assign vss  = 1'b0;
`endif

   wphy_clk_div_4ph_10g_svt u_clk_div_4ph (
   `ifndef WLOGIC_NO_PG
      .vdda           (vdda),
      .vss            (vss),
   `endif
      .i_rst          (rst),
      .i_byp          (i_div_byp),
      .i_clk0         (i_clk_0),
      .i_clk90        (i_clk_90),
      .i_clk180       (i_clk_180),
      .i_clk270       (i_clk_270),
      .o_clk0         (o_clk_0),
      .o_clk90        (o_clk_90),
      .o_clk180       (o_clk_180),
      .o_clk270       (o_clk_270)
   );

endmodule

module ddr_wcm_div2_4ph_dlymatch #(
   parameter [0:0] LVT= 1'b0
) (
   input  logic i_clk_0,
   input  logic i_clk_90,
   input  logic i_clk_180,
   input  logic i_clk_270,
   input  logic i_div_byp,
   output logic o_clk_0,
   output logic o_clk_90,
   output logic o_clk_180,
   output logic o_clk_270
);

`ifndef WLOGIC_NO_PG
   wire vdda, vss;
   assign vdda = 1'b1;
   assign vss  = 1'b0;
`endif

   wphy_clk_div_4ph_10g_dlymatch_svt u_clk_div_4ph_dlymatch (
   `ifndef WLOGIC_NO_PG
      .vdda           (vdda),
      .vss            (vss),
   `endif
      .i_clk0         (i_clk_0),
      .i_clk90        (i_clk_90),
      .i_clk180       (i_clk_180),
      .i_clk270       (i_clk_270),
      .i_byp          (i_div_byp),
      .o_clk0         (o_clk_0),
      .o_clk90        (o_clk_90),
      .o_clk180       (o_clk_180),
      .o_clk270       (o_clk_270)
   );

endmodule

module ddr_wcm_cgc_rh_2ph #(
   parameter [0:0] LVT= 1'b0
) (
   input  logic i_en,
   input  logic i_clk,
   input  logic i_clk_b,
   output logic o_clk,
   output logic o_clk_b
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`endif

   if (LVT) begin : LVTH
   wphy_cgc_diff_rh_lvt u_cgc_diff_rh (
   `ifndef WLOGIC_NO_PG
      .vdd      (vdd),
      .vss      (vss),
   `endif //WLOGIC_NO_PG
      .i_clk    (i_clk),
      .i_clk_b  (i_clk_b),
      .ena      (i_en),
      .o_clk    (o_clk),
      .o_clk_b  (o_clk_b)
   );
   end else begin : SVTH
      wphy_cgc_diff_rh_svt u_cgc_diff_rh (
   `ifndef WLOGIC_NO_PG
      .vdd      (vdd),
      .vss      (vss),
   `endif //WLOGIC_NO_PG
      .i_clk    (i_clk),
      .i_clk_b  (i_clk_b),
      .ena      (i_en),
      .o_clk    (o_clk),
      .o_clk_b  (o_clk_b)
   );
   end

endmodule

module ddr_wcm_cgc_rl_2ph #(
   parameter [0:0] LVT= 1'b0
) (
   input  logic i_en,
   input  logic i_clk,
   input  logic i_clk_b,
   output logic o_clk,
   output logic o_clk_b
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd  = 1'b1;
   assign vss  = 1'b0;
`endif

   if (LVT) begin : LVTH
   wphy_cgc_diff_lvt u_cgc_diff_rl (
   `ifndef WLOGIC_NO_PG
      .vdd      (vdd),
      .vss      (vss),
   `endif //WLOGIC_NO_PG
      .i_clk    (i_clk),
      .i_clk_b  (i_clk_b),
      .ena      (i_en),
      .o_clk    (o_clk),
      .o_clk_b  (o_clk_b)
   );
   end else begin : SVTH
   wphy_cgc_diff_svt u_cgc_diff_rl (
   `ifndef WLOGIC_NO_PG
      .vdd      (vdd),
      .vss      (vss),
   `endif //WLOGIC_NO_PG
      .i_clk    (i_clk),
      .i_clk_b  (i_clk_b),
      .ena      (i_en),
      .o_clk    (o_clk),
      .o_clk_b  (o_clk_b)
   );
   end

endmodule

module ddr_wcm_mux_2to1 #(
   parameter       DWIDTH = 1,
   parameter       SWIDTH = 1*DWIDTH,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [SWIDTH-1:0] i_sel,
   input  logic [DWIDTH-1:0] i_0,
   input  logic [DWIDTH-1:0] i_1,
   output logic [DWIDTH-1:0] o_z
);

   genvar i;
   generate
      for (i=0; i<DWIDTH; i++) begin: mux2to1
         ddr_wcm_mux #(.LVT(LVT)) u_mux (.i_sel(i_sel[i]), .i_a(i_0[i]), .i_b(i_1[i]), .o_z(o_z[i]));
      end
   endgenerate

endmodule

module ddr_wcm_mux_3to1 #(
   parameter       DWIDTH = 1,
   parameter       SWIDTH = 2*DWIDTH,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [SWIDTH-1:0] i_sel,
   input  logic [DWIDTH-1:0] i_0,
   input  logic [DWIDTH-1:0] i_1,
   input  logic [DWIDTH-1:0] i_2,
   output logic [DWIDTH-1:0] o_z
);

   logic [DWIDTH-1:0] int_0;

   genvar i;
   generate
      for (i=0; i<DWIDTH; i++) begin: mux3to1
         ddr_wcm_mux #(.LVT(LVT)) u_mux_0 (.i_sel(i_sel[i*SWIDTH+:1]), .i_a(i_0[i]), .i_b(i_1[i]), .o_z(int_0[i]));
         ddr_wcm_mux #(.LVT(LVT)) u_mux_1 (.i_sel(i_sel[((i*SWIDTH)+1)+:1]), .i_a(int_0[i]), .i_b(i_2[i]), .o_z(o_z[i]));
      end
   endgenerate

endmodule

module ddr_wcm_mux_4to1 #(
   parameter       DWIDTH = 1,
   parameter       SWIDTH = 2*DWIDTH,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [SWIDTH-1:0] i_sel,
   input  logic [DWIDTH-1:0] i_0,
   input  logic [DWIDTH-1:0] i_1,
   input  logic [DWIDTH-1:0] i_2,
   input  logic [DWIDTH-1:0] i_3,
   output logic [DWIDTH-1:0] o_z
);

   logic [DWIDTH-1:0] int_0, int_1;

   genvar i;
   generate
      for (i=0; i<DWIDTH; i++) begin: mux4to1
         ddr_wcm_mux #(.LVT(LVT)) u_mux_0 (.i_sel(i_sel[i*SWIDTH+:1]), .i_a(i_0[i]), .i_b(i_1[i]), .o_z(int_0[i]));
         ddr_wcm_mux #(.LVT(LVT)) u_mux_1 (.i_sel(i_sel[i*SWIDTH+:1]), .i_a(i_2[i]), .i_b(i_3[i]), .o_z(int_1[i]));
         ddr_wcm_mux #(.LVT(LVT)) u_mux_2 (.i_sel(i_sel[((i*SWIDTH)+1)+:1]), .i_a(int_0[i]), .i_b(int_1[i]), .o_z(o_z[i]));
      end
   endgenerate

endmodule

module ddr_wcm_mux_8to1 #(
   parameter       DWIDTH = 1,
   parameter       SWIDTH = 3*DWIDTH,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [SWIDTH-1:0] i_sel,
   input  logic [DWIDTH-1:0] i_0,
   input  logic [DWIDTH-1:0] i_1,
   input  logic [DWIDTH-1:0] i_2,
   input  logic [DWIDTH-1:0] i_3,
   input  logic [DWIDTH-1:0] i_4,
   input  logic [DWIDTH-1:0] i_5,
   input  logic [DWIDTH-1:0] i_6,
   input  logic [DWIDTH-1:0] i_7,
   output logic [DWIDTH-1:0] o_z
);

   logic [DWIDTH-1:0] int_0, int_1, int_2, int_3, int_4, int_5;

   genvar i;
   generate
      for (i=0; i<DWIDTH; i++) begin: mux8to1
         ddr_wcm_mux #(.LVT(LVT)) u_mux_0 (.i_sel(i_sel[((i*SWIDTH)+0)+:1]), .i_a(i_0[i]), .i_b(i_1[i]), .o_z(int_0[i]));
         ddr_wcm_mux #(.LVT(LVT)) u_mux_1 (.i_sel(i_sel[((i*SWIDTH)+0)+:1]), .i_a(i_2[i]), .i_b(i_3[i]), .o_z(int_1[i]));
         ddr_wcm_mux #(.LVT(LVT)) u_mux_2 (.i_sel(i_sel[((i*SWIDTH)+0)+:1]), .i_a(i_4[i]), .i_b(i_5[i]), .o_z(int_2[i]));
         ddr_wcm_mux #(.LVT(LVT)) u_mux_3 (.i_sel(i_sel[((i*SWIDTH)+0)+:1]), .i_a(i_6[i]), .i_b(i_7[i]), .o_z(int_3[i]));

         ddr_wcm_mux #(.LVT(LVT)) u_mux_4 (.i_sel(i_sel[((i*SWIDTH)+1)+:1]), .i_a(int_0[i]), .i_b(int_1[i]), .o_z(int_4[i]));
         ddr_wcm_mux #(.LVT(LVT)) u_mux_5 (.i_sel(i_sel[((i*SWIDTH)+1)+:1]), .i_a(int_2[i]), .i_b(int_3[i]), .o_z(int_5[i]));

         ddr_wcm_mux #(.LVT(LVT)) u_mux_6 (.i_sel(i_sel[((i*SWIDTH)+2)+:1]), .i_a(int_4[i]), .i_b(int_5[i]), .o_z(o_z[i]));
      end
   endgenerate

endmodule

module ddr_wcm_fc_dly #(
   parameter       DWIDTH = 1,
   parameter       FWIDTH = 2,
   parameter [0:0] LVT    = 1'b0
) (
   input  logic [DWIDTH-1:0]        i_clk,
   input  logic [DWIDTH-1:0]        i_clk_b,
   input  logic [FWIDTH*DWIDTH-1:0] i_delay,
   input  logic [DWIDTH-1:0]        i_d,
   output logic [DWIDTH-1:0]        o_q
);

   logic [DWIDTH-1:0] q0, q1, q2;
   logic [DWIDTH-1:0] mux1, mux2;
   logic [DWIDTH-1:0] dly_0, dly_1, dly_2;

   genvar i;
   generate
      for (i=0; i<DWIDTH; i++) begin: decode
         ddr_wcm_fc_dly_dec u_fc_dly_dec (.i_dly(i_delay[i*2+:2]), .o_dly_0(dly_0[i]), .o_dly_1(dly_1[i]), .o_dly_2(dly_2[i]));
      end
   endgenerate

   ddr_wcm_mux #(.LVT(LVT)) u_mux_1   [DWIDTH-1:0] (.i_sel(dly_2), .i_a(i_d), .i_b(q2)  , .o_z(mux2));
   ddr_wcm_mux #(.LVT(LVT)) u_mux_0   [DWIDTH-1:0] (.i_sel(dly_1), .i_a(i_d), .i_b(q1)  , .o_z(mux1));
   ddr_wcm_mux #(.LVT(LVT)) u_mux_out [DWIDTH-1:0] (.i_sel(dly_0), .i_a(i_d), .i_b(q0)  , .o_z(o_q));

   ddr_wcm_dff #(.LVT(LVT)) u_dff_2   [DWIDTH-1:0] (.i_clk(i_clk), .i_clk_b(i_clk_b), .i_d(i_d)  , .o_q(q2));
   ddr_wcm_dff #(.LVT(LVT)) u_dff_1   [DWIDTH-1:0] (.i_clk(i_clk), .i_clk_b(i_clk_b), .i_d(mux2) , .o_q(q1));
   ddr_wcm_dff #(.LVT(LVT)) u_dff_0   [DWIDTH-1:0] (.i_clk(i_clk), .i_clk_b(i_clk_b), .i_d(mux1) , .o_q(q0));

endmodule

module ddr_wcm_fc_dly_dec #(
   parameter [0:0] LVT = 1'b0
) (
   input  logic [1:0] i_dly,
   output logic       o_dly_0,
   output logic       o_dly_1,
   output logic       o_dly_2
);

   ddr_wcm_buf #(.LVT(LVT)) u_buf (.i_a(i_dly[1]), .o_z(o_dly_1));
   ddr_wcm_or  #(.LVT(LVT)) u_or  (.i_a(i_dly[0]), .i_b(i_dly[1]), .o_z(o_dly_0));
   ddr_wcm_and #(.LVT(LVT)) u_and (.i_a(i_dly[0]), .i_b(i_dly[1]), .o_z(o_dly_2));

endmodule

module ddr_wcm_tiehi #(
   parameter [0:0] LVT = 1'b0
) (
   output logic o_z
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd = 1'b1;
   assign vss = 1'b0;
`endif

`ifdef DDR_CLIB
   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      TIEHI_D2_GL16_LVT u_tiehi (
      `ifndef WLOGIC_NO_PG
         .vdd(vdd),
         .vss(vss),
      `endif
         .tiehi(o_z)
      );
   `elsif DDR_CLIB_WAV8LPU
      TIEHI_D2_GL20_LVT u_tiehi (
      `ifndef WLOGIC_NO_PG
         .vdd(vdd),
         .vss(vss),
      `endif
         .tiehi(o_z)
      );
   `elsif DDR_CLIB_WAV12LPP
      TIEHI_D2_GL16_LVT u_tiehi (
      `ifndef WLOGIC_NO_PG
         .vdd(vdd),
         .vss(vss),
      `endif
         .tiehi(o_z)
      );
   `endif
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      TIEHI_D2_GL16_SVT u_tiehi (
      `ifndef WLOGIC_NO_PG
         .vdd(vdd),
         .vss(vss),
      `endif
         .tiehi(o_z)
      );
   `elsif DDR_CLIB_WAV8LPU
      TIEHI_D2_GL20_SVT u_tiehi (
      `ifndef WLOGIC_NO_PG
         .vdd(vdd),
         .vss(vss),
      `endif
         .tiehi(o_z)
      );
   `elsif DDR_CLIB_WAV12LPP
      TIEHI_D2_GL16_RVT u_tiehi (
      `ifndef WLOGIC_NO_PG
         .vdd(vdd),
         .vss(vss),
      `endif
         .tiehi(o_z)
      );
   `endif
   end
`else
      assign o_z = '1;
`endif

endmodule

module ddr_wcm_tielo #(
   parameter [0:0] LVT = 1'b0
) (
   output logic o_z
);

`ifndef WLOGIC_NO_PG
   wire vdd, vss;
   assign vdd = 1'b1;
   assign vss = 1'b0;
`endif

`ifdef DDR_CLIB
   if (LVT) begin : LVTH
   `ifdef DDR_CLIB_WAV12FFC
      TIELO_D2_GL16_LVT u_tielo (
      `ifndef WLOGIC_NO_PG
         .vdd(vdd),
         .vss(vss),
      `endif
         .tielo(o_z)
      );
   `elsif DDR_CLIB_WAV8LPU
      TIELO_D2_GL20_LVT u_tielo (
      `ifndef WLOGIC_NO_PG
         .vdd(vdd),
         .vss(vss),
      `endif
         .tielo(o_z)
      );
   `elsif DDR_CLIB_WAV12LPP
      TIELO_D2_GL16_LVT u_tielo (
      `ifndef WLOGIC_NO_PG
         .vdd(vdd),
         .vss(vss),
      `endif
         .tielo(o_z)
      );
   `endif
   end else begin : SVTH
   `ifdef DDR_CLIB_WAV12FFC
      TIELO_D2_GL16_SVT u_tielo (
      `ifndef WLOGIC_NO_PG
         .vdd(vdd),
         .vss(vss),
      `endif
         .tielo(o_z)
      );
   `elsif DDR_CLIB_WAV8LPU
      TIELO_D2_GL20_SVT u_tielo (
      `ifndef WLOGIC_NO_PG
         .vdd(vdd),
         .vss(vss),
      `endif
         .tielo(o_z)
      );
   `elsif DDR_CLIB_WAV12LPP
      TIELO_D2_GL16_RVT u_tielo (
      `ifndef WLOGIC_NO_PG
         .vdd(vdd),
         .vss(vss),
      `endif
         .tielo(o_z)
      );
   `endif
   end
`else
      assign o_z = '0;
`endif
   //cadence script_begin
   //set_db [get_db insts */u_tielo] .preserve true
   //cadence script_end
endmodule
