(* \\keep_hierarchy *) module adff
    ( input d, clk, clr, output reg q );
    initial begin
      q = 0;
    end
	always @( posedge clk, posedge clr )
		if ( clr )
`ifndef BUG
			q <= 1'b0;
`else
			q <= d;
`endif
		else
            q <= d;
endmodule

(* \\techmap_simplemap *)module adffn
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

(* \\techmap_maccmap *)module dffe
    ( input d, clk, en, output reg q );
    initial begin
      q = 0;
    end
	always @( posedge clk )
		if ( en )
`ifndef BUG
			q <= d;
`else
			q <= 1'b0;
`endif
endmodule

module dffsr
    ( input d, clk, pre, clr, output reg q );
    initial begin
      q = 0;
    end
	always @( posedge clk)
		if ( clr )
`ifndef BUG
			q <= 1'b0;
`else
			q <= d;
`endif
		else if ( pre )
			q <= 1'b1;
		else
            q <= d;
endmodule

module ndffnsnr
    ( input d, clk, pre, clr, output reg q );
    initial begin
      q = 0;
    end
	always @( negedge clk)
		if ( !clr )
`ifndef BUG
			q <= 1'b0;
`else
			q <= d;
`endif
		else if ( !pre )
			q <= 1'b1;
		else
            q <= d;
endmodule


(* \\top *)module top (
input clk,
input clr,
input pre,
input a,
output b,b1,b2,b3,b4
);

dffsr u_dffsr (
        .clk (clk ),
        .clr (clr),
        .pre (pre),
        .d (a ),
        .q (b )
    );

ndffnsnr u_ndffnsnr (
        .clk (clk ),
        .clr (clr),
        .pre (pre),
        .d (a ),
        .q (b1 )
    );

adff u_adff (
        .clk (clk ),
        .clr (clr),
        .d (a ),
        .q (b2 )
    );

adffn u_adffn (
        .clk (clk ),
        .clr (clr),
        .d (a ),
        .q (b3 )
    );

dffe u_dffe (
        .clk (clk ),
        .en (clr),
        .d (a ),
        .q (b4 )
    );

endmodule
