module dffs
    ( input d, clk, pre, output reg q );
    initial begin
      q = 0;
    end
	always @( posedge clk, negedge pre )
		if ( !pre )
`ifndef BUG
			q <= 1'b1;
`else
			q <= d;
`endif
		else
            q <= d;
endmodule

module dffr
    ( input d, clk, clr, output reg q );
    initial begin
      q = 0;
    end
	always @( posedge clk, negedge clr )
		if ( !clr )
`ifndef BUG
			q <= 1'b0;
`else
			q <= d;
`endif
		else
            q <= d;
endmodule

module top (
input clk,
input clr,
input pre,
input a,
output b,b1
);

dffs u_dffs (
        .clk (clk ),
        .pre (pre),
        .d (a ),
        .q (b )
    );

dffr u_dffr (
        .clk (clk ),
        .clr (clr ),
        .d (a ),
        .q (b1 )
    );

endmodule
