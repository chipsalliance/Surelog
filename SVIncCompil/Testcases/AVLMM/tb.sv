`timescale 1ps / 1ps

module tb ();

   reg clk    = 1'b0;
   reg reset  = 1'b1;
   
   localparam  CLOCK_PERIOD            = 100; // Clock period in ps
   localparam  INITIAL_RESET_CYCLES    = 10;  // Number of cycles to reset when simulation starts
   
   avlm_avls_2x2 dut(
      .clk_clk(clk),
      .reset_reset_n(~reset)
   );
   
   test_program  tp();
   
   // Clock signal generator
   always begin
      #(CLOCK_PERIOD / 2);
      clk = ~clk;
   end
   
   // Initial reset
   initial begin
      repeat(INITIAL_RESET_CYCLES) @(posedge clk);
      reset = 1'b0;
   end

endmodule 