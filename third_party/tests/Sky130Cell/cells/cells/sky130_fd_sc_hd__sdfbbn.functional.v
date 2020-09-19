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


`ifndef SKY130_FD_SC_HD__SDFBBN_FUNCTIONAL_V
`define SKY130_FD_SC_HD__SDFBBN_FUNCTIONAL_V

/**
 * sdfbbn: Scan delay flop, inverted set, inverted reset, inverted
 *         clock, complementary outputs.
 *
 * Verilog simulation functional model.
 */

`timescale 1ns / 1ps
`default_nettype none

// Import user defined primitives.
`include "../../models/udp_mux_2to1/sky130_fd_sc_hd__udp_mux_2to1.v"
`include "../../models/udp_dff_nsr/sky130_fd_sc_hd__udp_dff_nsr.v"

`celldefine
module sky130_fd_sc_hd__sdfbbn (
    Q      ,
    Q_N    ,
    D      ,
    SCD    ,
    SCE    ,
    CLK_N  ,
    SET_B  ,
    RESET_B
);

    // Module ports
    output Q      ;
    output Q_N    ;
    input  D      ;
    input  SCD    ;
    input  SCE    ;
    input  CLK_N  ;
    input  SET_B  ;
    input  RESET_B;

    // Local signals
    wire RESET  ;
    wire SET    ;
    wire CLK    ;
    wire buf_Q  ;
    wire mux_out;

    //                            Delay       Name       Output   Other arguments
    not                                       not0      (RESET  , RESET_B                 );
    not                                       not1      (SET    , SET_B                   );
    not                                       not2      (CLK    , CLK_N                   );
    sky130_fd_sc_hd__udp_mux_2to1             mux_2to10 (mux_out, D, SCD, SCE             );
    sky130_fd_sc_hd__udp_dff$NSR  `UNIT_DELAY dff0      (buf_Q  , SET, RESET, CLK, mux_out);
    buf                                       buf0      (Q      , buf_Q                   );
    not                                       not3      (Q_N    , buf_Q                   );

endmodule
`endcelldefine

`default_nettype wire
`endif  // SKY130_FD_SC_HD__SDFBBN_FUNCTIONAL_V