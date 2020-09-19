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


`ifndef SKY130_FD_SC_HD__A21BO_FUNCTIONAL_V
`define SKY130_FD_SC_HD__A21BO_FUNCTIONAL_V

/**
 * a21bo: 2-input AND into first input of 2-input OR,
 *        2nd input inverted.
 *
 *        X = ((A1 & A2) | (!B1_N))
 *
 * Verilog simulation functional model.
 */

`timescale 1ns / 1ps
`default_nettype none

`celldefine
module sky130_fd_sc_hd__a21bo (
    X   ,
    A1  ,
    A2  ,
    B1_N
);

    // Module ports
    output X   ;
    input  A1  ;
    input  A2  ;
    input  B1_N;

    // Local signals
    wire nand0_out  ;
    wire nand1_out_X;

    //   Name   Output       Other arguments
    nand nand0 (nand0_out  , A2, A1         );
    nand nand1 (nand1_out_X, B1_N, nand0_out);
    buf  buf0  (X          , nand1_out_X    );

endmodule
`endcelldefine

`default_nettype wire
`endif  // SKY130_FD_SC_HD__A21BO_FUNCTIONAL_V