module top
    ( input d, clk, output reg q );

    wire u;


	always @( posedge clk )
            q <= d;
endmodule
