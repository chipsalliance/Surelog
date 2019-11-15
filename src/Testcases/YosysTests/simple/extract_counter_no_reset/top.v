module top    (
out,
clk,
reset
);
    output [7:0] out;
    input clk, reset;
    reg [7:0] out;

	initial out <= 0 ;


    always @(posedge clk)
			out <= out + 1;


endmodule
