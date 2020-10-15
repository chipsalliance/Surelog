module ibex_multdiv_fast (
    input logic [33:0] imd_val_q_i[2]
);

  logic [31:0] op_denominator_q;
  assign op_denominator_q = imd_val_q_i[1][31:0];

endmodule

