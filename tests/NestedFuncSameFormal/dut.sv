// Nested package function calls whose formals share a name — outer(inner(x))
// with both formals `g` and NON-constant actuals — sent ExprEval into
// getValue -> reduceExpr -> getValue on the same name until the stack was
// exhausted (OpenTitan aes_sbox_dom: aes_scale_omega2_gf2p2(aes_square_gf2p2(..))).
package gf_pkg;
  function automatic logic [1:0] outer(logic [1:0] g);
    logic [1:0] d;
    d[1] = g[0];
    d[0] = g[1] ^ g[0];
    return d;
  endfunction
  function automatic logic [1:0] inner(logic [1:0] g);
    logic [1:0] d;
    d[1] = g[0];
    d[0] = g[1];
    return d;
  endfunction
endpackage
module dut (input logic [1:0] a, b, output logic [1:0] x, y, z);
  import gf_pkg::*;
  assign x = outer(inner(a ^ b));
  assign y = outer(inner(a));
  assign z = outer(inner(2'b10));   // constant actual: still folds
endmodule
