`define D #1
module test(input clk);
reg d;
always @(posedge clk)
    d <= `D (~d);
endmodule
