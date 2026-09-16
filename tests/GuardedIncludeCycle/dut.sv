// Two headers that include each other, each protected by the standard
// `ifndef GUARD / `define GUARD idiom.  The second visit expands to nothing,
// so this is legal and common (caliptra-rtl's caliptra_prim_assert.sv and
// caliptra_prim_flop_macros.sv do exactly this).  Erroring the first time a
// file reappears on the include stack rejected it; only a file reaching the
// stack a THIRD time is genuinely unguarded recursion.
`include "a.svh"

module top(input logic a, output logic y);
`ifdef FROM_A
`ifdef FROM_B
  assign y = a;
`endif
`endif
endmodule
