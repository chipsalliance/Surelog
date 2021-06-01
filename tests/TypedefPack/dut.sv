package lc_ctrl_pkg;
  typedef enum logic [3:0] {
    On  = 4'b1010,
    Off = 4'b0101
  } lc_tx_e;

  typedef lc_tx_e lc_tx_t;
endpackage : lc_ctrl_pkg

module prim_lc_sender (
  input  [3:0] lc_en_i,
  output lc_ctrl_pkg::lc_tx_t lc_en_o
);
  assign lc_en_o = lc_ctrl_pkg::lc_tx_t'(lc_en_i);
endmodule : prim_lc_sender
