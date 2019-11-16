module top(A, clk, rst);
   input clk, rst;
   output A;

  parameter GPIO_COUNT = 16;
  initial begin
    if (GPIO_COUNT < 0 || GPIO_COUNT > 16) begin
      $display("Parameter Error: GPIO_COUNT must be in range 0..16");
      $finish;
    end
  end

endmodule
