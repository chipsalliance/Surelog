module top;
`define MAX(_a, _b) ((_a) > (_b) ? (_a) : (_b))
localparam integer X = `MAX($clog2(1 << 17) - 18, 0);
initial $display("%d", X);
endmodule
