/*
 * Copyright 2020 The SkyWater PDK Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * SPDX-License-Identifier: Apache-2.0
*/


`ifndef SKY130_FD_SC_HD__MACRO_SPARECELL_FUNCTIONAL_V
`define SKY130_FD_SC_HD__MACRO_SPARECELL_FUNCTIONAL_V

/**
 * macro_sparecell: Macro cell for metal-mask-only revisioning,
 *                  containing inverter, 2-input NOR, 2-input NAND,
 *                  and constant cell.
 *
 * Verilog simulation functional model.
 */

`timescale 1ns / 1ps
`default_nettype none

// Import sub cells.
`include "../conb/sky130_fd_sc_hd__conb.v"
`include "../nor2/sky130_fd_sc_hd__nor2.v"
`include "../inv/sky130_fd_sc_hd__inv.v"
`include "../nand2/sky130_fd_sc_hd__nand2.v"

`celldefine
module sky130_fd_sc_hd__macro_sparecell (
    LO
);

    // Module ports
    output LO;

    // Local signals
    wire nor2left ;
    wire invleft  ;
    wire nor2right;
    wire invright ;
    wire nd2left  ;
    wire nd2right ;
    wire tielo    ;
    wire net7     ;

    //                       Name    Output         Other arguments
    sky130_fd_sc_hd__inv_2   inv0   (.A(nor2left) , .Y(invleft)                );
    sky130_fd_sc_hd__inv_2   inv1   (.A(nor2right), .Y(invright)               );
    sky130_fd_sc_hd__nor2_2  nor20  (.B(nd2left)  , .A(nd2left), .Y(nor2left)  );
    sky130_fd_sc_hd__nor2_2  nor21  (.B(nd2right) , .A(nd2right), .Y(nor2right));
    sky130_fd_sc_hd__nand2_2 nand20 (.B(tielo)    , .A(tielo), .Y(nd2right)    );
    sky130_fd_sc_hd__nand2_2 nand21 (.B(tielo)    , .A(tielo), .Y(nd2left)     );
    sky130_fd_sc_hd__conb_1  conb0  (.LO(tielo)   , .HI(net7)                  );
    buf                      buf0   (LO           , tielo                      );

endmodule
`endcelldefine

`default_nettype wire
`endif  // SKY130_FD_SC_HD__MACRO_SPARECELL_FUNCTIONAL_V