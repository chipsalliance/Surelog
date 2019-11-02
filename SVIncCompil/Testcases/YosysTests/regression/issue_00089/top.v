module top(A, clk, rst);
   input clk, rst;
   output A;

   always @(posedge clk, posedge rst) begin
      A <= '0';
   end;  // << like this

endmodule
