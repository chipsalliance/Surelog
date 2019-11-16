module top(input clk, d, output reg q);
wire ce = 1'b1;
always @(negedge clk)
    if (ce) q <= d;
endmodule
