package aes_pkg;
typedef enum logic {
  CIPH_FWD = 1'b0,
  CIPH_INV = 1'b1
} ciph_op_e;
endpackage

module mix_columns (
  input  aes_pkg::ciph_op_e    op_i
);
endmodule

module cipher_core(
  input  aes_pkg::ciph_op_e    op_i
);
  import aes_pkg::*;
  mix_columns key_mix_columns (
    .op_i   ( CIPH_INV            )
  );
endmodule
