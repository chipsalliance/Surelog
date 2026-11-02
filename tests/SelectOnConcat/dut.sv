// A select applied to a concatenation primary (LRM A.8.4): the range_expression
// after the concatenation was dropped, so `{b, c}[9:6]` compiled as `{b, c}`.
// The select is a nameless part_select / bit_select whose actual is the
// concatenation operation.
module top(input logic [7:0] b, input logic [7:0] c, output logic [3:0] a,
           output logic d, output logic [3:0] e);
  assign a = {b, c}[9:6];
  assign d = {b, c}[8];
  assign e = {2{c}}[11:8];
endmodule
