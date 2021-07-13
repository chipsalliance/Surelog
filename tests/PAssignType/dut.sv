package aes_pkg;
typedef struct packed {
  logic[31:0] manual_operation;
} ctrl_reg_t;

parameter ctrl_reg_t CTRL_RESET = '{
  manual_operation: '0
};
endpackage

module subreg #(
  parameter logic [31:0] RESVAL = '0
) ();
endmodule

module shadow #(
  parameter logic [31:0] RESVAL = '0
) ();
  subreg #(.RESVAL(RESVAL)) commit_reg();
endmodule

module aes_core;
  import aes_pkg::*;
  ctrl_reg_t ctrl_q;
  shadow #(.RESVAL(CTRL_RESET)) shadow_reg();
endmodule // aes_core

