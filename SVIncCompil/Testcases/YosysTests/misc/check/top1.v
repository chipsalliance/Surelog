module top
    ( input d, clk, output reg q );

    wire u;
    wire s;

    assign u = s;

	assign u = d;

	assign u = clk;

	always @( posedge clk )
            q <= u;
endmodule
