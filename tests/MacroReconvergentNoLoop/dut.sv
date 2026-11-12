// A macro body that reaches one macro along two paths of DIFFERENT length is
// not recursive: `A expands `D directly and again through `B -> `C -> `D.
// The preprocessor's loop check used to report PP0115 "Recursive macro
// definition" on such a reconvergence once `A was expanded a second time in
// the same top-level use (`T), and every macro after it read as undefined.
// OpenPiton's l2.tmp.h / define.tmp.h hit it on XY_WIDTH (78 modules).
`define E 1
`define D (`E)
`define C `D
`define B `C
`define A (`D + `B)
`define T `A:`A
module dut(input logic [7:0] i, output logic o);
  assign o = i[`T];
endmodule
