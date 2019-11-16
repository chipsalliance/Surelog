module top(clk, in, out);
    parameter DEPTH=10;
    input wire clk, in;
    output reg out;

    (* anyseq *) reg [1:0] X;
	always @(posedge clk)
	begin
		assert($rose(in) == ((in)&&(!$past(in))));
		assert($fell(in) == ((!in)&&($past(in))));
	end
endmodule
