module top (
input [7:0] S,
input [255:0] D,
output M256
);

assign M256 = D[S];

endmodule
