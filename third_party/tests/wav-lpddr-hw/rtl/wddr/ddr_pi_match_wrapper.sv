
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
`include "ddr_pi_match_wrapper_define.vh"

import ddr_global_pkg::*;

module ddr_pi_match_wrapper #(
   parameter PWIDTH = 9
)
(
   input  logic [PWIDTH-1:0]  i_pi_cfg,
   input i_clk180,
   input i_clk0,
   output o_clk,
   output o_clk_b
);


`ifndef WLOGIC_NO_PG
   wire vdda, vss;
   assign vdda = 1'b1;
   assign vss = 1'b0;
`endif


   wphy_pi_dly_match_4g u_pi_match (
      .out(o_clk),
      .outb(o_clk_b),
      .xcpl(i_pi_cfg[`DDR_ANA_PI_MATCH_XCPL_RANGE]),
      .gear(i_pi_cfg[`DDR_ANA_PI_MATCH_GEAR_RANGE]),
      .ena(i_pi_cfg[`DDR_ANA_PI_MATCH_EN_RANGE]),
      .clk180(i_clk180),
      .clk0(i_clk0)
`ifndef WLOGIC_NO_PG
      ,.vdda(vdda),
      .vss(vss)
`endif
   );

endmodule
