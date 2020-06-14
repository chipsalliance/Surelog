// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Implementation of a Read-Only Memory (ROM) primitive for Xilinx FPGAs
 *
 * This implementation of a ROM primitive is coded as outlined in UG 901 to
 * enable Xilinx Vivado infer Block RAM (BRAM) or LUT RAM from it. No mapping
 * target is forced; depending on the Width, Depth and other factors Vivado
 * chooses a mapping target.
 *
 * It is possible to force the mapping to BRAM or distributed RAM by using the
 * ROM_STYLE directive in an XDC file.
 */
module prim_xilinx_rom #(
  parameter  int Width     = 32,
  parameter  int Depth     = 2048, // 8kB default
  parameter  int Aw        = $clog2(Depth)
) (
  input                        clk_i,
  input        [Aw-1:0]        addr_i,
  input                        cs_i,
  output logic [Width-1:0]     dout_o,
  output logic                 dvalid_o

);

  















    // ROM is not initialized
    always_ff @(posedge clk_i) begin
      dout_o <= '0;
    end
  

  always_ff @(posedge clk_i) begin
    dvalid_o <= cs_i;
  end


  ////////////////
  // ASSERTIONS //
  ////////////////

  // Control Signals should never be X
  

endmodule
