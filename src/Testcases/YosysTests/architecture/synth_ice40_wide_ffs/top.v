module adff
    ( input [3:0] d, input clk, clr, output reg [3:0] q );
    initial begin
      q = 4'b0000;
    end
	always @( posedge clk, posedge clr )
		if ( clr )
`ifndef BUG
			q <= 4'b0110;
`else
			q <= d;
`endif
		else
            q <= d;
endmodule

module adffn
    ( input [3:0] d, input clk, clr, output reg [3:0] q );
    initial begin
      q = 4'b0100;
    end
	always @( posedge clk, negedge clr )
		if ( !clr )
`ifndef BUG
			q <= 4'b0100;
`else
			q <= d;
`endif
		else
            q <= d;
endmodule

module dffe
    ( input [3:0] d, input clk, en, output reg [3:0] q );
    initial begin
      q = 4'b0010;
    end
	always @( posedge clk)
		if ( en )
`ifndef BUG
			q <= d;
`else
			q <= 4'b0000;
`endif
endmodule

module dffsr
    ( input [3:0] d, input clk, pre, clr, output reg [3:0] q );
    initial begin
      q = 0;
    end
	always @( posedge clk, negedge pre, posedge clr )
		if ( clr )
`ifndef BUG
			q <= 4'b1010;
`else
			q <= d;
`endif
		else if ( !pre )
			q <= 4'b0101;
		else
            q <= d;
endmodule

module dffs
    ( input [3:0] d, input clk, pre, output reg [3:0] q );
    initial begin
      q = 1;
    end
	always @( posedge clk, negedge pre )
		if ( !pre )
			q <= 4'b1111;
		else
            q <= d;
endmodule


module dffse
    ( input [3:0] d, input clk, en, pre, output reg [3:0] q );
    initial begin
      q = 1;
    end
	always @( posedge clk )
		if ( !pre )
			q <= 4'b0101;
		else
			if ( en )
				q <= d;
endmodule

module ndffnsnr
    ( input [3:0] d, input clk, pre, clr, output reg [3:0] q );
    initial begin
      q = 0;
    end
	always @( negedge clk, posedge pre, negedge clr )
		if ( !clr )
`ifndef BUG
			q <= 4'b0010;
`else
			q <= d;
`endif
		else if ( pre )
			q <= 4'b1101;
		else
            q <= d;
endmodule

module top (
input clk,
input clr,
input pre,
input [3:0] a,
output [3:0] b,b1,b2,b3,b4
);

wire b5,b6;

dffsr u_dffsr (
        .clk (clk ),
        .clr (clr),
        .pre (pre),
        .d (a ),
        .q (b )
    );

dffs u_dffs (
        .clk (clk ),
        .pre (pre),
        .d (a ),
        .q (b5 )
    );

dffse u_dffse (
        .clk (clk ),
        .pre (pre),
        .en (en),
        .d (a ),
        .q (b6 )
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
