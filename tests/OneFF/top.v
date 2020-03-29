module ff_tb; 
  reg clk;
  reg div;
  initial begin
    $monitor("@%0dns clk = %0d, %0d",$time,clk, div);
    #100 $finish();
  end
  
  initial 
  begin 
    clk = 0; 
    div = 0;
  end 
    
  always 
    #5 clk = !clk; 
 
  always @(posedge clk)
    begin
      div <= !div;
    end
  
endmodule
