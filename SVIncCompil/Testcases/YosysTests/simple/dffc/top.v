module dffcp
    ( input d, clk, pre, clr, output reg q );
	always @( posedge clk)
		if ( pre )
			q <= 1'b1;
		else if ( clr )
			q <= 1'b0;
		else
            q <= d;
endmodule


module top (
input clk,
input a,
input c,
output b
);

dffcp u_dffcp (
        .clk (clk ),
        .clr (c ),
`ifndef BUG
        .pre (1'b1),
`else
        .pre (1'b0),
`endif
        .d (a ),
        .q (b )
    );

endmodule
