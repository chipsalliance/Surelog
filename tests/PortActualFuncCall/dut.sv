// A port actual that is a FUNCTION CALL (OpenTitan ascon_core:
// `.key_i(swap_endianess_byte(key_in))`).  The call must stay a func_call in
// the model: reducing it to the function BODY leaks the function's formals
// into the instance scope, leaving the child's input undriven.
package p;
  function automatic logic [31:0] swap_bytes(logic [31:0] v);
    return {v[7:0], v[15:8], v[23:16], v[31:24]};
  endfunction
endpackage
module child (
  input  logic [31:0] a_i,
  input  logic [31:0] c_i,
  output logic [31:0] y_o
);
  assign y_o = a_i ^ c_i;
endmodule
module top import p::*; (
  input  logic [31:0] d_i,
  output logic [31:0] y_o
);
  child u (.a_i(swap_bytes(d_i)), .c_i(swap_bytes(d_i ^ 32'h1234_5678)), .y_o(y_o));
endmodule
