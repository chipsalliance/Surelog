// A `let` call is inlined with its formals substituted by the actuals --
// by NAME for `.x(a)`, by POSITION otherwise, and a formal used twice gets
// the actual twice.  Before the fix the inlined body kept `x`, `y`, `z` as
// unbound references.
module top(input logic [3:0] a, input logic [3:0] b, input logic [3:0] c,
           output logic d, output logic e, output logic [3:0] f);
  let op(x, y, z) = |((x | y) & z);
  let twice(v) = v + v;
  assign d = op(.x(a), .y(b), .z(c));
  assign e = op(c, b, a);
  assign f = twice(a);
endmodule
