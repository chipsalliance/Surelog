interface sw_test_status_if;
  logic data_valid;
  assign data_valid = 1'b1;

  bit sw_test_done;
  initial begin
     sw_test_done = 1'b1;
  end
  

endinterface

module top;
   sw_test_status_if u_sw();
endmodule // top
