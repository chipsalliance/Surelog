module alert_handler_reg_wrap;
  for (genvar k = 0; k < 1; k++) begin : gen_alert_cause
    assign hw2reg.alert_cause[k].d  = 1'b1;
  end
endmodule

