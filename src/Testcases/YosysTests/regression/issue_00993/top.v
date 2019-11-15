module top(y, clk, wire1);
   output wire [1:0] y;
   input wire        clk;
   input wire [1:0]  wire1;
   reg [1:0]         reg1 = 0;
   reg [1:0]         reg2 = 0;
   always @(posedge clk) begin
      reg1 <= wire1 == 1;
   end
   always @(posedge clk) begin
      reg2 <= 1 >> reg1[1:1];
   end
   assign y = reg2;
endmodule
