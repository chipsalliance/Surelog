module top (y, clk, wire4);
   output wire [1:0] y;
   input             clk;
   input signed      wire4;
   reg [1:0]  reg10 = 0;
   always @(posedge clk) begin
      reg10 <= wire4;
   end
   assign y = reg10;
endmodule
