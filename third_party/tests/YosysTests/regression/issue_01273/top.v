module top (
    input [5:0] S,
    input [63:0] D,
    output M256
);
    assign M256 = D[S];
endmodule
