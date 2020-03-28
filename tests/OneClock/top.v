module counter_tb; 
  reg clk, in1, in2;

  initial 
  begin 
    clk = 0; 
  end 
    
  always 
    #5 clk = !clk; 
    
  
endmodule
