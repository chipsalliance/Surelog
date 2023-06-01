
module top();

   for (i = 3; i > 0 ; i--) begin
      assign tmp[i] = 1'b1;
   end

   for (i = 0; i < 2 ; i++) begin
      assign tmp[i] = 1'b1;
   end

   for (i = 0; i < 2 ; i+=1) begin
      assign tmp[i] = 1'b1;
   end

  for (i = 3; i > 0 ; i-=1) begin
      assign tmp[i] = 1'b1;
   end
   
endmodule
