// A size cast whose WIDTH is a bare parameter name (`W'(expr)`) is compiled
// with a logic_typespec spanning W bits; its constant fold dropped the
// wildcard digits of the operand (`'h0_b00?` -> 2816), unlike the literal
// width `20'(expr)` and the parenthesised `(W)'(expr)` forms.  All three must
// keep the `?` nibble: the decoder's `inside {pattern}` matches 16 addresses.
package pk;
  localparam W = 20;
  localparam a_gp = W'('h0_b00?);
  localparam b_gp = 20'('h0_b00?);
  localparam c_gp = (W)'('h0_b00?);
endpackage
module top import pk::*; (input logic [19:0] addr, output logic [2:0] m);
  assign m[0] = addr inside {a_gp};
  assign m[1] = addr inside {b_gp};
  assign m[2] = addr inside {c_gp};
endmodule
