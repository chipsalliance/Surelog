module t;

  typedef struct packed {
    logic        q;
  } rstmgr_reg2hw_sw_rst_ctrl_n_mreg_t;

  typedef struct packed {
    rstmgr_reg2hw_sw_rst_ctrl_n_mreg_t [0:0] sw_rst_ctrl_n;
  } rstmgr_reg2hw_t;

  rstmgr_reg2hw_t reg2hw;
  rstmgr_reg2hw_sw_rst_ctrl_n_mreg_t [0:0] sw_rst_ctrl_n;

  logic X = reg2hw.sw_rst_ctrl_n[0].q;
  logic Y = sw_rst_ctrl_n[0].q;
endmodule;
