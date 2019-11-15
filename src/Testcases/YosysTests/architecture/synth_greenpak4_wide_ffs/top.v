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

module gp_dff
    ( input d, input clk, clr, output reg q );

    wire nq;

    GP_DFF u_gp_dffr (d,clk,nq);

    GP_INV u_gp_inv (nq,q);

endmodule

module gp_dffr
    ( input d, input clk, clr, output reg q );

    wire nq;

    GP_DFFR u_gp_dffr (d,clk,clr,nq);

    GP_INV u_gp_inv (nq,q);

endmodule

module gp_dffs
    ( input d, input clk, clr, output reg q );

    wire nq;

    GP_DFFS u_gp_dffs (d,clk,clr,nq);

    GP_INV u_gp_inv (nq,q);

endmodule

module gp_dffsi
    ( input d, input clk, clr, output reg q );

    wire nq;

    GP_DFFSI u_gp_dffs (d,clk,clr,nq);

    GP_INV u_gp_inv (nq,q);

endmodule

module gp_latchs
    ( input d, input clk, clr, output reg q );

    wire nq;

    GP_DLATCHS u_gp_dffs (d,clk,clr,nq);

    GP_INV u_gp_inv (nq,q);

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

wire [3:0] b5,b6,b7,b8,bn,a_i;

dffsr u_dffsr (
        .clk (clk ),
        .clr (clr),
        .pre (pre),
        .d (~a ),
        .q (bn )
    );

assign b = ~bn;

dffs u_dffs (
        .clk (clk ),
        .pre (pre),
        .d (a ),
        .q (b5 )
    );

gp_dffr u_gp_dffr (
        .clk (clk ),
        .clr (clr),
        .d (a ),
        .q (b7[0] )
    );

gp_dff u_gp_dff (
        .clk (clk ),
        .clr (clr),
        .d (a ),
        .q (b8[0] )
    );

gp_dffs u_gp_dffs (
        .clk (clk ),
        .clr (clr),
        .d (a ),
        .q (b7[1] )
    );

gp_dffsi u_gp_dffsi (
        .clk (clk ),
        .clr (clr),
        .d (a ),
        .q (b7[2] )
    );

gp_latchs u_gp_latchs (
        .clk (clk ),
        .clr (clr),
        .d (a ),
        .q (b7[3] )
    );

dffse u_dffse (
        .clk (clk ),
        .pre (pre),
        .en (en),
        .d (~a ),
        .q (b6 )
    );

ndffnsnr u_ndffnsnr (
        .clk (clk ),
        .clr (~clr),
        .pre (~pre),
        .d (a ),
        .q (b1 )
    );

adff u_adff (
        .clk (~clk ),
        .clr (~clr),
        .d (~a ),
        .q (b2 )
    );

assign a_i[1:0] = a[1:0];
assign a_i[3:2] = ~a[3:2];

adffn u_adffn (
        .clk (clk ),
        .clr (~clr),
        .d (a_i ),
        .q (b3 )
    );

dffe u_dffe (
        .clk (~clk ),
        .en (clr),
        .d (a ),
        .q (b4 )
    );

endmodule
