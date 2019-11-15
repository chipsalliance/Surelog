module top
    ( input d, clk, output reg q );
	always @( posedge clk )
            q <= d;
endmodule

module top2
    ( input d, clk, output reg q );
	always @( posedge clk )
            q <= d;
endmodule
