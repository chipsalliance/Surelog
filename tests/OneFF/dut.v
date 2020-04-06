
module dut  (input d,
              input rstn,
              input clk,
              output reg q);
 
  always @ (posedge clk or negedge rstn) 
      begin
       if (!rstn)
          q <= 0;
       else
          q <= d;
      end    
endmodule
 
