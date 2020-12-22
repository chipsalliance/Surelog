module top();
  
  `define USE_BOOTMODE_TEST
   `ifdef USE_BOOTMODE_TEST
      assign a= b;
      assign c= d;/*
   `else
      assign a= 1'b0;
      assign c= 1'b0;*/
   `endif

endmodule
