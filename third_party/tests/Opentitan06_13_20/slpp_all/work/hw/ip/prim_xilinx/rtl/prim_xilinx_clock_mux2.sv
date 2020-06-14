// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions












































































































































module prim_xilinx_clock_mux2 (
  input        clk0_i,
  input        clk1_i,
  input        sel_i,
  output logic clk_o
);

  // for more info, refer to the Xilinx technology primitives userguide, e.g.:
  // ug953-vivado-7series-libraries.pdf
  // ug974-vivado-ultrascale-libraries.pdf
  BUFGMUX bufgmux_i (
    .S  ( sel_i  ),
    .I0 ( clk0_i ),
    .I1 ( clk1_i ),
    .O  ( clk_o  )
  );

  // make sure sel is never X (including during reset)
  // need to use ##1 as this could break with inverted clocks that
  // start with a rising edge at the beginning of the simulation.
  
  

endmodule : prim_xilinx_clock_mux2
