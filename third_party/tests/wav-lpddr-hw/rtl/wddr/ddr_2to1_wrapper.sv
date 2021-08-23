
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

module ddr_2to1_wrapper (
   output logic o_z,
   input  logic i_clk,
   input  logic i_clk_b,
   input  logic i_even,
   input  logic i_odd
);

`ifndef WLOGIC_NO_PG
   wire vdda, vss;
   assign vdda = 1'b1;
   assign vss  = 1'b0;
`endif

   wphy_2to1_14g_rvt u_2to1 (
      .o_z          (o_z),
      .i_clk        (i_clk),
      .i_clk_b      (i_clk_b),
      .i_datar      (i_even),
      .i_dataf      (i_odd)
`ifndef WLOGIC_NO_PG
      ,.vdda        (vdda),
      .vss          (vss)
`endif
   );

endmodule
