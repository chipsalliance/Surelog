// Test for `bind <hierarchical_identifier>` syntax (IEEE 1800-2017
// 23.11 form 2: bind_target_instance).  Surelog used to reject
// `bind $root.top.foo_i ...` and `bind top.foo_i ...` with
// "no viable alternative at input 'bind \$root'".  The
// bind_directive rule now accepts hierarchical_identifier as the
// target, matching the LRM.
//
// Sourced from yosys/tests/bind/hier.sv.

module foo (input logic a, input logic b, output logic c);
endmodule

module bar (input a, input b, output c);
  assign c = a ^ b;
endmodule

module top ();
  logic u, v, w;
  foo foo_i (.a (u), .b (v), .c (w));
endmodule

// Hierarchical target with $root prefix.
bind $root.top.foo_i bar bound_i (.*);
