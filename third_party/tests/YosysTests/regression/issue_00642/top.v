module top(clk, in, out);
    parameter DEPTH=10;
    input wire clk, in;
    output reg out;

    always @(posedge clk)
        out <= $past(in,DEPTH-1);
endmodule
