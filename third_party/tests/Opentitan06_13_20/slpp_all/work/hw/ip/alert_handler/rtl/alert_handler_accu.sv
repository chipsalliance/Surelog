// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module accumulates incoming alert triggers. Once the current accumulator
// value is greater or equal the accumulator threshold, the next occurence of
// class_trig_i will trigger escalation.
//
// Note that the accumulator is implemented using a saturation counter which
// does not wrap around.
//

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions












































































































































module alert_handler_accu import alert_pkg::*; (
  input                        clk_i,
  input                        rst_ni,
  input                        class_en_i,   // class enable
  input                        clr_i,        // clear the accumulator
  input                        class_trig_i, // increments the accu
  input        [AccuCntDw-1:0] thresh_i,     // escalation trigger threshold
  output logic [AccuCntDw-1:0] accu_cnt_o,   // output of current accu value
  output logic                 accu_trig_o   // escalation trigger output
);

  logic trig_gated;
  logic [AccuCntDw-1:0] accu_d, accu_q;

  assign trig_gated = class_trig_i & class_en_i;

  assign accu_d = (clr_i)                    ? '0 : // clear
                  (trig_gated && !(&accu_q)) ? accu_q + 1'b1 : // saturate counter at maximum
                                               accu_q;

  assign accu_trig_o = (accu_q >= thresh_i) & trig_gated;

  assign accu_cnt_o = accu_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      accu_q <= '0;
    end else begin
      accu_q <= accu_d;
    end
  end


  ////////////////
  // Assertions //
  ////////////////

  
  

endmodule : alert_handler_accu
