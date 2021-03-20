module top(input clk_i, output b);

  dut #(.CLKFBOUT_PHASE(12.50/3.0)) d (
  .a(clk_i),
  .b(b));
endmodule

module dut #(
  parameter real CLKFBOUT_PHASE = 1142.500
) (input a, output b);

  parameter err = CLKFBOUT_PHASE / 0;

parameter f = 9;
parameter r = 5.7;
parameter average_delay = (r + f)/2;

parameter A1 = 0.1 * 0.5;

parameter A2 = 0.1 - 0.5;

parameter A3 = - 0.6;

parameter A4 = 1 + 5;

parameter A5 = 1 - 5;

parameter A6 = 2 * 5;

parameter A7 = 5 / 2;

   if (A1 == 0.05) begin
      GOOD good1();
   end
   
   if (A2 == -0.4) begin
      GOOD good2();
   end
   
   if (A3 == -0.6) begin
      GOOD good3();
   end
   
   if (A4 == 6) begin
      GOOD good4();
   end
  
   if (A5 == -4) begin
      GOOD good5();
   end
   
   if (A6 == 10) begin
      GOOD good6();
   end
   
   if (A7 == 2) begin
      GOOD good7();
   end
     

endmodule
