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


`ifndef SKY130_FD_SC_HD__O41A_FUNCTIONAL_V
`define SKY130_FD_SC_HD__O41A_FUNCTIONAL_V

/**
 * o41a: 4-input OR into 2-input AND.
 *
 *       X = ((A1 | A2 | A3 | A4) & B1)
 *
 * Verilog simulation functional model.
 */

`timescale 1ns / 1ps
`default_nettype none

`celldefine
module sky130_fd_sc_hd__o41a (
    X ,
    A1,
    A2,
    A3,
    A4,
    B1
);

    // Module ports
    output X ;
    input  A1;
    input  A2;
    input  A3;
    input  A4;
    input  B1;

    // Local signals
    wire or0_out   ;
    wire and0_out_X;

    //  Name  Output      Other arguments
    or  or0  (or0_out   , A4, A3, A2, A1 );
    and and0 (and0_out_X, or0_out, B1    );
    buf buf0 (X         , and0_out_X     );

endmodule
`endcelldefine

`default_nettype wire
`endif  // SKY130_FD_SC_HD__O41A_FUNCTIONAL_V