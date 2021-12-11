module alert_handler_reg_wrap;
  for (genvar k = 0; k < 1; k++) begin : gen_alert_cause
    assign hw2reg.alert_cause[k].d  = 1'b1;
  end
endmodule


module top;
  typedef struct packed {
    int x;
  } struct_t;

  struct_t [1:0][2:0] a;
  
  assign a[0][0].x[0] = 1;
endmodule
