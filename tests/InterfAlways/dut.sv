interface sw_test_status_if(output int x);
   always begin
      x = 10;
   end
endinterface

module top(output int o);
   sw_test_status_if u_sw(.x(o));
endmodule // top
