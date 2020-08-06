package dm ;

typedef enum logic [1:0] {
  DTM_NOP   = 2'h0,
  DTM_READ  = 2'h1,
  DTM_WRITE = 2'h2
} dtm_op_e;

endpackage


module dm_csrs ();

  dm::dtm_op_e dtm_op;
  assign dtm_op = dm::dtm_op_e'(dmi_req_i.op);

endmodule

