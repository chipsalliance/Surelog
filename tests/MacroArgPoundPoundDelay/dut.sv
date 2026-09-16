// A `##N` delay inside a PARENTHESIZED macro actual: `paired_parens` in the
// preprocessor grammar has to accept the pound-delay tokens, else the whole
// `MacroInstanceWithArgs` alternative fails, the call falls back to
// `MacroInstanceNoArgs` and every argument is reported missing.
`define ASSERT(name, prop, clk = clk, rst = rst) \
  name: assert property (@(posedge clk) disable iff (rst) (prop));

module top(input logic clk, rst, a, b);
  `ASSERT(CHK0, (a ##1 b) |-> b, clk, !rst)
  `ASSERT(CHK1, ((a && !b) ##2 !a) |-> b, clk, !rst)
endmodule
