module rr_arb_tree #(
  parameter type         DataType   = logic [DataWidth-1:0]) ();
  DataType data;

endmodule


module top ();
 typedef struct packed {
    logic [2:0]   result;
    logic status;
    logic            tag;
  } output_t;

 rr_arb_tree #(
    .DataType  ( output_t     )
  ) i_arbiter ();


endmodule
