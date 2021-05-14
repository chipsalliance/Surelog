package tlul_pkg;
  typedef struct packed {
    logic  [10:0]  d_source;
  } tl_d2h_t;
endpackage
module dut ();
  tlul_pkg::tl_d2h_t drsp_fifo_o;
  logic [5:0] hfifo_rspid;
  assign hfifo_rspid = drsp_fifo_o.d_source[8:3];
endmodule
