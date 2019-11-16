module top    (
out,
clk,
reset
);
    output [7:0] out;
    input clk, reset;
    reg [7:0] out;

    always @(posedge clk, posedge reset)
		if (reset) begin
			out <= 8'b0 ;
		end else
`ifndef BUG
			out <= out + 1;
`else
			out <= out - 1'bZ;
`endif
//FORCE

endmodule
