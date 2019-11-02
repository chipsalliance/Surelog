module dff
    ( input d, clk, output reg q );
    initial begin
      q = 0;
    end
	always @( posedge clk )
            q <= d;
endmodule


module adff
    ( inout d, clk, clr, output reg q );
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

module adffn
    ( input d, clk, clr, output reg q );
    parameter S=0;
    initial begin
      q = 1'bX;
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

module dffe
    ( input d, clk, en, output reg q );
    parameter Z=1'bZ;
    initial begin
      q = Z;
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
	always @( posedge clk, posedge pre, posedge clr )
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
    ( d, clk, pre, clr, q );
    parameter s=2;
    parameter l=1;
    input [s-1:l] d; 
    input clk, pre, clr; 
    output reg [s-1:l] q;
    
    initial begin
      q = 2'b11;
    end
	always @( negedge clk, negedge pre, negedge clr )
		if ( !clr )
`ifndef BUG        
			q <= 2'b00;
`else        
			q <= d;
`endif
		else if ( !pre )
			q <= 2'b11;
		else
            q <= d;
endmodule

module top (
input clk,
input clr,
input pre,
input a,
output b,b1,b2,b3,b4
);

wire a1,b11;

dffsr u_dffsr (
        .clk (clk ),
        .clr (clr),
        .pre (pre),
        .d (a ),
        .q (b )
    );
    
ndffnsnr #(4) u_ndffnsnr (
        .clk (clk ),
        .clr (clr),
        .pre (pre),
        .d ({a,a1} ),
        .q ({b1,b11} )
    );
    
defparam u_ndffnsnr.l = 0;
    
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
