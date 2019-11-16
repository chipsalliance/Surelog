module tc(clk,A,B,C,D,E,F);
input clk;
input[3:0] A,B,C,E;
output reg[7:0] D,F;
always @(posedge clk)
begin
D = A + B + C;
F = A + B + E;
end
endmodule
