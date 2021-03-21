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

parameter A8 = 10 % 3;
 
parameter A9 = 10.3 % 2.1;
    
parameter A10 = 10.3 % 2;

parameter A11 = 2 ** 8;

parameter A12 = 2.1 ** 8;

parameter A13  = A8 ? A12 : A11;

parameter A14 = 20 % 0;

function incr_d;
   integer incr_d;
   incr_d = 10.1;
   incr_d++;
   return incr_d;
endfunction

parameter A15 = incr_d();
   
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
     
 if (A8 == 1) begin
      GOOD good8();
 end

  if ((A9 > 1.8) && (A9 < 2)) begin
     GOOD good9();
  end
  
  if ((A10 >= 0.3) && (A10 <= 0.3)) begin
     GOOD good10();
  end

  if (A11 == 256) begin
     GOOD good11();
  end

  if ((A12 > 378) && (A12 < 378.23)) begin
     GOOD good12();
  end

  if ((A13 > 378) && (A13 < 378.23)) begin
     GOOD good13();
  end

 if ((A15 > 11) && (A15 <= 11.1)) begin
     GOOD good15();
  end

endmodule
