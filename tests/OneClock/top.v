module counter_tb; 
  reg clk, in1, in2, out;

  initial 
  begin 
    clk = 0; 
  end 
    
  always 
    #5 clk = !clk; 

  always 
    #5 out = in1 & in2;   
  
endmodule
