module top(output int a);
   import "DPI-C" task test_output_argument(output int o);

   initial begin
      test_output_argument(a);
   end
endmodule
