// A real literal may carry digit separators (LRM 5.7.2), including after the
// fraction and before the exponent.  The value must keep its exponent: all of
// these are small, so every integral target rounds to 0 -- the bug stored
// 236.123 (strtod stopped at the first `_`) and gave 236.
module top(output logic [31:0] a1, output logic [31:0] a2, output logic [31:0] a3,
           output logic [31:0] a4);
  localparam real R1 = 236.123_763_e-12;
  localparam real R2 = 1_0.5e-1;      // 1.05
  localparam real R3 = 2.1_5e2;       // 215
  assign a1 = 236.123_763_e-12;
  assign a2 = R1;
  assign a3 = R2;
  assign a4 = R3;
endmodule
