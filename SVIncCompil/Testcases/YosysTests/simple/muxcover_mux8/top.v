module top (
input [5:0] S,
input [63:0] D,
output M256
);
`ifndef BUG
assign M256 = D[S];
`else
assign M256 = S[D];
`endif

endmodule
