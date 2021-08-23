
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

module ddr_clkmux_3to1_diff_wrapper # (
  parameter SLVT_TYPE = 0
) (
   output logic       o_c,
   output logic       o_t,
   input  logic       i_01_c,
   input  logic       i_01_t,
   input  logic       i_10_c,
   input  logic       i_10_t,
   input  logic       i_11_c,
   input  logic       i_11_t,
   input  logic [1:0] i_sel
);

`ifndef WLOGIC_NO_PG
   wire vdda, vss;
   assign vdda = 1'b1;
   assign vss  = 1'b0;
`endif

   generate
   if (SLVT_TYPE) begin : SLVT_MUX  // High speed clock mux
    wphy_clkmux_3to1_diff_slvt u_clkmux_3to1
       (
         .out_c         (o_c),
         .out_t         (o_t),
         .in01_c        (i_01_c),
         .in01_t        (i_01_t),
         .in10_c        (i_10_c),
         .in10_t        (i_10_t),
         .in11_c        (i_11_c),
         .in11_t        (i_11_t),
         .s             (i_sel)
   `ifdef WLOGIC_NO_PG
   `else
         ,.vdda
         ,.vss
   `endif //WLOGIC_NO_PG
       );
   end else begin : RVT_MUX
    wphy_clkmux_3to1_diff u_clkmux_3to1
       (
         .out_c         (o_c),
         .out_t         (o_t),
         .in01_c        (i_01_c),
         .in01_t        (i_01_t),
         .in10_c        (i_10_c),
         .in10_t        (i_10_t),
         .in11_c        (i_11_c),
         .in11_t        (i_11_t),
         .s             (i_sel)
   `ifdef WLOGIC_NO_PG
   `else
         ,.vdda
         ,.vss
   `endif //WLOGIC_NO_PG
       );
   end
   endgenerate

endmodule
