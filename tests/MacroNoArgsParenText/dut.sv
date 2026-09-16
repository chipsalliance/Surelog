// A macro that declares NO formal arguments is not a macro CALL when followed
// by `(`: the parenthesized text is ordinary source that must be reproduced in
// full.  Emitting only the first comma-separated piece dropped every port but
// the first (caliptra-rtl's `module `CALIPTRA_ICG (...)`).
`define ICG my_gate

module `ICG (
    input logic clk,
    input logic en,
    output logic clk_cg
);
  logic en_lat;
  always_latch if (!clk) en_lat = en;
  assign clk_cg = clk && en_lat;
endmodule

module top(input logic clk, en, output logic clk_cg);
  my_gate u (.clk(clk), .en(en), .clk_cg(clk_cg));
endmodule
