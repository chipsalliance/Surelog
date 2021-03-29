module top();
    parameter p = 1'b0;
   if (p == "BLAH") begin
      GOOD_BLAH good();
   end
   if (p == 4'b1001) begin
      GOOD_BIN1 good();
   end
   if (p == 4'b1011) begin
      GOOD_BIN2 good();
   end 
   if (p == 'hFF) begin
      GOOD_HEXA good();
   end
   if (p == -12) begin
      GOOD_MINUS12 good();
   end
   if (p == 12) begin
      GOOD_12 good();
   end
   if (p == 12.12) begin
      GOOD_REAL12 good();
   end
   if (p == 0) begin
      GOOD_0 good();
   end
endmodule
