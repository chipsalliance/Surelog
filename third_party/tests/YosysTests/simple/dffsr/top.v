module dffsr
    ( input d, clk, pre, clr, output reg q );
	always @( posedge clk, posedge pre, negedge clr )
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
output b
);

dffsr u_dffsr (
        .clk (clk ),
`ifndef BUG        
        .clr (1'b1),
        .pre (1'b1),
`else        
        .clr (1'b0),
        .pre (1'b0),
`endif
        .d (a ),
        .q (b )
    );

endmodule
