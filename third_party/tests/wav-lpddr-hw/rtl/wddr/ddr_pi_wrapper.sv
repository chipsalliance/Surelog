
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
`include "ddr_pi_wrapper_define.vh"

import ddr_global_pkg::*;

module ddr_pi_wrapper #(
   parameter PWIDTH = 15
)
(
   input  logic [PWIDTH-1:0]  i_pi_cfg,
   input i_clk270,
   input i_clk180,
   input i_clk90,
   input i_clk0,
   output o_clk,
   output o_clk_b
);

   logic [15:0] code_therm;
   logic [1:0] quad;

`ifndef WLOGIC_NO_PG
   wire vdda, vss;
   assign vdda = 1'b1;
   assign vss = 1'b0;
`endif

`ifndef DDR_PI_CSR_DEC
   ddr_pi_b2t_dec u_pi_decoder (
      .i_code_bin(i_pi_cfg[`DDR_ANA_PI_CODE_RANGE]),
      .o_code_therm(code_therm),
      .o_quad(quad)
   );
`else
   assign code_therm = i_pi_cfg[`DDR_ANA_PI_THERM_RANGE];
   assign quad = i_pi_cfg[`DDR_ANA_PI_QUAD_RANGE];
`endif

`ifdef DDRPHY_14G_ANA
   wphy_pi_14g u_pi (
      .out(o_clk),
      .outb(o_clk_b),
      .xcpl(i_pi_cfg[`DDR_ANA_PI_XCPL_RANGE]),
      .quad(quad[1:0]),
      .gear(i_pi_cfg[`DDR_ANA_PI_GEAR_RANGE]),
      .ena(i_pi_cfg[`DDR_ANA_PI_EN_RANGE]),
      .code(code_therm[15:0]),
      .clk270(i_clk270),
      .clk180(i_clk180),
      .clk90(i_clk90),
      .clk0(i_clk0)
`ifndef WLOGIC_NO_PG
      ,.vdda(vdda),
      .vss(vss)
`endif
   );
`else
   wphy_pi_4g u_pi (
      .out(o_clk),
      .outb(o_clk_b),
      .xcpl(i_pi_cfg[`DDR_ANA_PI_XCPL_RANGE]),
      .quad(quad[1:0]),
      .gear(i_pi_cfg[`DDR_ANA_PI_GEAR_RANGE]),
      .ena(i_pi_cfg[`DDR_ANA_PI_EN_RANGE]),
      .code(code_therm[15:0]),
      .clk270(i_clk270),
      .clk180(i_clk180),
      .clk90(i_clk90),
      .clk0(i_clk0)
`ifndef WLOGIC_NO_PG
      ,.vdda(vdda),
      .vss(vss)
`endif
   );
`endif

endmodule
