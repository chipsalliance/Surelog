package aes_pkg;
typedef struct packed {
  logic[31:0] manual_operation;
} ctrl_reg_t;

parameter ctrl_reg_t CTRL_RESET = '{
  manual_operation: '0
};
endpackage

module prim_subreg #(
  parameter logic [31:0] RESVAL = '0
) ();
endmodule

module prim_subreg_shadow #(
  parameter logic [31:0] RESVAL = '0
) ();
  prim_subreg #(.RESVAL(RESVAL)) committed_reg();
endmodule

module aes_core;
  import aes_pkg::*;
  ctrl_reg_t ctrl_q;
  prim_subreg_shadow #(.RESVAL(CTRL_RESET)) ctrl_shadowed_reg();
endmodule // aes_core
