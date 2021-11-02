module stream_arbiter_flushable #(
    parameter type      DATA_T = logic,   // Vivado requires a default value for type parameters.
    parameter integer   N_INP = -1,       // Synopsys DC requires a default value for parameters.
    parameter           ARBITER = "rr"    // "rr" or "prio"
) (output DATA_T             oup_data_o);

endmodule

module stream_arbiter #(
    parameter type      DATA_T = logic,   // Vivado requires a default value for type parameters.
    parameter integer   N_INP = -1,       // Synopsys DC requires a default value for parameters.
    parameter           ARBITER = "rr") ();

  stream_arbiter_flushable #(
    .DATA_T   (DATA_T),
    .N_INP    (N_INP),
    .ARBITER  (ARBITER)
  ) i_arb ();

endmodule

module axi_node_arbiter #(
  parameter int unsigned AUX_WIDTH = 5, // Synopsys DC requires a default value for parameters.
  parameter int unsigned ID_WIDTH = 5,
  parameter int unsigned N_MASTER = 10) ();

  typedef struct packed {
    logic [AUX_WIDTH-1:0] aux;
    logic [ID_WIDTH-1:0]  id;
  } axi_meta_t;

 stream_arbiter #(
    .DATA_T (axi_meta_t),
    .N_INP  (N_MASTER)
  ) i_arb_inp ( );

endmodule // axi_node_arbiter
