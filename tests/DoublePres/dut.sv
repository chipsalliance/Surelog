
module top(input clk_i, output b);

  dut #(.CLKFBOUT_PHASE(12.50/3.0)) d (
  .a(clk_i),
  .b(b));
endmodule

module dut #(
  parameter real CLKFBOUT_PHASE = 1142.500
) (input a, output b);
  assign a = b;
endmodule
