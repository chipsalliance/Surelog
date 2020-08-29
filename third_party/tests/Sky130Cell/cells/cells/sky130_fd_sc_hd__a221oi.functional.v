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


`ifndef SKY130_FD_SC_HD__A221OI_FUNCTIONAL_V
`define SKY130_FD_SC_HD__A221OI_FUNCTIONAL_V

/**
 * a221oi: 2-input AND into first two inputs of 3-input NOR.
 *
 *         Y = !((A1 & A2) | (B1 & B2) | C1)
 *
 * Verilog simulation functional model.
 */

`timescale 1ns / 1ps
`default_nettype none

`celldefine
module sky130_fd_sc_hd__a221oi (
    Y ,
    A1,
    A2,
    B1,
    B2,
    C1
);

    // Module ports
    output Y ;
    input  A1;
    input  A2;
    input  B1;
    input  B2;
    input  C1;

    // Local signals
    wire and0_out  ;
    wire and1_out  ;
    wire nor0_out_Y;

    //  Name  Output      Other arguments
    and and0 (and0_out  , B1, B2                );
    and and1 (and1_out  , A1, A2                );
    nor nor0 (nor0_out_Y, and0_out, C1, and1_out);
    buf buf0 (Y         , nor0_out_Y            );

endmodule
`endcelldefine

`default_nettype wire
`endif  // SKY130_FD_SC_HD__A221OI_FUNCTIONAL_V