module alat
    ( input d, en, clr, output reg q );
    initial begin
      q = 0;
    end
	always @(*)
		if ( clr )
`ifndef BUG
			q <= 1'b0;
`else
			q <= d;
`endif
		else if (en)
            q <= d;
endmodule

module alatn
    ( input d, en, clr, output reg q );
    initial begin
      q = 0;
    end
	always @(*)
		if ( !clr )
`ifndef BUG
			q <= 1'b0;
`else
			q <= d;
`endif
		else if (!en)
            q <= d;
endmodule

module latsr
    ( input d, en, pre, clr, output reg q );
    initial begin
      q = 0;
    end
	always @(*)
		if ( clr )
`ifndef BUG
			q <= 1'b0;
`else
			q <= d;
`endif
		else if ( pre )
			q <= 1'b1;
		else if ( en )
            q <= d;
endmodule

module nlatsr
    ( input d, en, pre, clr, output reg q );
    initial begin
      q = 0;
    end
	always @(*)
		if ( !clr )
`ifndef BUG
			q <= 1'b0;
`else
			q <= d;
`endif
		else if ( !pre )
			q <= 1'b1;
		else if ( !en )
            q <= d;
endmodule

module dlatchsr (EN, SET, CLR, D, Q);

    input EN;
    input SET, CLR, D;
    output reg Q;

    always @*
        if (CLR)
            Q = 0;
        else if (SET)
            Q = 1;
        else if (EN)
            Q = D;

endmodule

module top (
input en,
input clr,
input pre,
input a,
output b,b1,b2,b3
);

latsr u_latsr (
        .en (en ),
        .clr (clr),
        .pre (pre),
        .d (a ),
        .q (b )
    );

nlatsr u_nlatsr (
        .en (en ),
        .clr (clr),
        .pre (pre),
        .d (a ),
        .q (b1 )
    );

alat u_alat (
        .en (en ),
        .clr (clr),
        .d (a ),
        .q (b2 )
    );

alatn u_alatn (
        .en (en ),
        .clr (clr),
        .d (a ),
        .q (b3 )
    );

endmodule
