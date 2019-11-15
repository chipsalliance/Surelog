module top    (
out,
clk,
reset
);
    output [7:0] out;
    input clk, reset;
    reg [7:0] out;

    always @(posedge clk)
		if (reset) begin
			out <= 8'b0 ;
		end else
			out <= out + 1;


endmodule
