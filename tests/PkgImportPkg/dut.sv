package otp_ctrl_pkg;
  typedef struct packed {
    logic [1:0] pwr_seq;
  } otp_ast_req_t;
endpackage : otp_ctrl_pkg

package otp_ctrl_part_pkg;
  import otp_ctrl_pkg::*;
endpackage : otp_ctrl_part_pkg

module otp_ctrl
  import otp_ctrl_pkg::*;
(
  output otp_ast_req_t otp_ast_pwr_seq_o,
  input  otp_ast_rsp_t otp_ast_pwr_seq_h_i
);
endmodule : otp_ctrl
