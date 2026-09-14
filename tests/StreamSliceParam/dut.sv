// Streaming operator whose slice size is a VALUE PARAMETER: `{<<W{a}}`.
// slice_size ::= simple_type | constant_expression, and a bare identifier
// parses as a simple_type (ps_type_identifier), so the slice size was compiled
// as $bits(<non-type>) = 0 — a full bit reversal instead of W-bit slices
// (prim_lfsr's NonLinearOut layer, `{<<LfsrIdxDw{col}}`).  All three outputs
// must reduce to the same 6-bit-slice reversal.
module StreamSliceParam (input logic [95:0] a, output logic [95:0] lit_o, output logic [95:0] par_o, output logic [95:0] fn_o);
  localparam int W = 6;
  typedef logic [15:0][5:0] col_t;
  function automatic col_t revcol(col_t col);
    return {<<W{col}};
  endfunction
  assign lit_o = {<<6{a}};
  assign par_o = {<<W{a}};
  assign fn_o  = revcol(a);
endmodule
module top;
  logic [95:0] a, l, p, f;
  StreamSliceParam u (.a(a), .lit_o(l), .par_o(p), .fn_o(f));
endmodule
