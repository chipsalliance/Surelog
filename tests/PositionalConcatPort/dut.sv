// A concatenation as a POSITIONAL port actual absorbed the FOLLOWING ports'
// actuals into its own high_conn.
//
//   inner u({r2, r1}, y);          // positional -> port `a` got {{r2,r1}, y}
//   inner u(.a({r2,r1}), .y(y));   // named      -> correct
//
// Positional connections share grammar with gate instantiations, so they are
// compiled through the paNet_lvalue path rather than the named-connection one.
// That case built its concatenation by starting at the node itself and walking
// SIBLINGS -- right when the caller passes the first ELEMENT of a net_lvalue
// concatenation, but wrong when the node IS the concatenation `{a, b}`, whose
// own child is another net_lvalue and whose siblings are the next ports'
// actuals.
//
// Port `y` still got its own correct high_conn, so the actual was duplicated
// and port `a` was over-wide; a consumer flattening {{r2,r1}, y} drove `a`
// with {r1, y}.
//
// Found on CORE-V Wally's aes64e/aes64d, which do
// `aesshiftrows64 srow({rs2,rs1}, ShiftRowsOut);`: SboxEIn[7:0] read undriven
// and the co-simulation diverged on 300 of 301 cycles.
module inner(input logic [15:0] a, output logic [7:0] y);
  assign y = a[7:0];
endmodule

module named_ref(input logic [15:0] a, output logic [7:0] y);
  assign y = a[7:0];
endmodule

module dut(input logic [7:0] r1, input logic [7:0] r2,
           output logic [7:0] y_pos, output logic [7:0] y_named);
  inner     u_pos({r2, r1}, y_pos);                 // the broken form
  named_ref u_named(.a({r2, r1}), .y(y_named));     // the control
endmodule
