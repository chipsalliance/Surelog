// This is purely a simulation test, no dut
module tb; 
  reg clk;

  initial begin
    $monitor("@%0dns clk = %0d",$time,clk);
    #100 $finish();
  end
  
  initial 
  begin 
    clk = 0; 
  end 
    
  always 
    #5 clk = !clk; 

 
endmodule
