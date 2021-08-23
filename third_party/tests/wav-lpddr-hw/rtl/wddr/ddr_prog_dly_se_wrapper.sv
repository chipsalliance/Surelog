
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
`include "ddr_prog_dly_se_wrapper_define.vh"

import ddr_global_pkg::*;

module ddr_prog_dly_se_wrapper #(
   parameter PWIDTH = 9
)  (
      output logic o_clk_b,
      input  logic [PWIDTH-1:0] i_prog_dly_cfg,
      input  logic i_clk
);

`ifndef WLOGIC_NO_PG
   wire vdda, vss;
   assign vdda = 1'b1;
   assign vss  = 1'b0;
`endif

   wphy_prog_dly_se_4g u_prog_dly_se (
      .outb          (o_clk_b),
      .i_ctrl        (i_prog_dly_cfg[`DDR_ANA_PROG_DLY_SE_CTRL_BIN_RANGE]),
      .ena           (i_prog_dly_cfg[`DDR_ANA_PROG_DLY_SE_EN_RANGE]),
      .gear          (i_prog_dly_cfg[`DDR_ANA_PROG_DLY_SE_GEAR_RANGE]),
      .in            (i_clk)
`ifndef WLOGIC_NO_PG
      ,.vdda         (vdda),
      .vss           (vss)
`endif
   );

endmodule
