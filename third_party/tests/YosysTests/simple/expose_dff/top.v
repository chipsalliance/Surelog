module dffr
    ( input d, clk, output reg q );
	always @( posedge clk )
            q <= d;
endmodule


module top (
input clk,
input a,
output b
);

dffr u_dffr (
        .clk (clk),
`ifndef BUG
        .d (a ),
`else
        .d (1'b1 ),
`endif
        .q (b )
    );

endmodule

