// A cast to a TYPE PARAMETER must use the type BOUND on the instance, not the
// parameter's default.  `sid_t'(NumPorts - 1)` under `parameter type sid_t =
// logic` overridden to a 3-bit type was typed as ONE bit: the two port actuals
// (compiled per instance) and the module-level assign (compiled once, reduced
// per instance) all folded to a 1-bit constant.  Expected: u_store.sid_i = 3,
// u_pf.sid_i = 4, sid_pf_o = 4, and the non-constant casts keep 3 bits.
module leaf #(parameter type sid_t = logic) (input sid_t sid_i, output logic [3:0] o);
  assign o = {1'b0, sid_i};
endmodule
module mid #(parameter int NumPorts = 4, parameter type sid_t = logic) (
    input logic [3:0] in4,
    output logic [3:0] o_store, output logic [3:0] o_pf, output sid_t sid_pf_o,
    output logic [3:0] o_dyn, output logic [3:0] o_dyn2);
  leaf #(.sid_t(sid_t)) u_store (.sid_i(sid_t'(NumPorts - 1)), .o(o_store));
  leaf #(.sid_t(sid_t)) u_pf    (.sid_i(sid_t'(NumPorts)),     .o(o_pf));
  leaf #(.sid_t(sid_t)) u_dyn   (.sid_i(sid_t'(in4 + 4'd1)),   .o(o_dyn));
  assign sid_pf_o = sid_t'(NumPorts);
  assign o_dyn2 = {1'b0, sid_t'(in4 + 4'd1)};
endmodule
module top (input logic [3:0] in4, output logic [3:0] o_store, output logic [3:0] o_pf,
            output logic [2:0] sid_pf_o, output logic [3:0] o_dyn, output logic [3:0] o_dyn2);
  typedef logic [2:0] my_sid_t;
  mid #(.NumPorts(4), .sid_t(my_sid_t)) u (.in4, .o_store, .o_pf, .sid_pf_o, .o_dyn, .o_dyn2);
endmodule
