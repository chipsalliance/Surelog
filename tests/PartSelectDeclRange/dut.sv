// Constant part-selects of vector PARAMETERS, folded by Surelog's ExprEval.
// The fold indexed the value's bits from the LSB as if every range were
// [N-1:0]: on [15:5] / [5:15] it read past the value and folded to an EMPTY
// constant (read as 0), and `-:` started one bit low even on [10:0]
// (`r[7 -: 5]` gave bits [6:2]).  YosysHQ/yosys#3689's localparam selects.
package pk;
  localparam bit [8:23] W = 16'hA5C3;
endpackage
module dut (
  output logic [4:0] a0, a1, a2, a3,
  output logic [4:0] b0, b1, b2,
  output logic [4:0] c0, c1, c2,
  output logic [3:0] d0, e0, e1,
  output logic [1:0] f0
);
  localparam [5:15]  p = 11'b10110011101;
  localparam [15:5]  q = 11'b10110011101;
  localparam [10:0]  r = 11'b10110011101;
  localparam [10:0]  s = 1693;
  localparam bit [3:10] t = 8'hC6;
  assign a0 = p[13 -: 5];
  assign a1 = p[9 +: 5];
  assign a2 = q[13 -: 5];
  assign a3 = q[9 +: 5];
  assign b0 = r[7 -: 5];
  assign b1 = s[7 -: 5];
  assign b2 = r[3 +: 5];
  assign c0 = p[9:13];
  assign c1 = q[13:9];
  assign c2 = p[11 +: 5];
  assign d0 = t[4 +: 4];
  assign e0 = pk::W[12 +: 4];
  assign e1 = pk::W[20 -: 4];
  assign f0 = r[7:6];
endmodule
