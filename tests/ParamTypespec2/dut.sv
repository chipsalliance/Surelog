package prim_esc_pkg;
  typedef struct packed {
    logic esc_p;
    logic esc_n;
  } esc_tx_t;

  parameter esc_tx_t ESC_TX_DEFAULT = '{esc_p:  1'b0,
                                        esc_n:  1'b1};

endpackage : prim_esc_pkg

module nmi_gen
   import prim_esc_pkg::*;
(
   input esc_tx_t [2:0] a,
   output int x
);
   assign x = int'(a);
endmodule // nmi_gen

module top(output int o);
   nmi_gen u_nmi_gen(
      .a({3{prim_esc_pkg::ESC_TX_DEFAULT}}),
      .x(o)
   );
endmodule // top
