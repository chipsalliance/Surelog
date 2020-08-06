/*
:name: sanity
:description: A simple module that should fail during parsing
:should_fail_because: syntaxerror line is not SV code
:tags: sanity
*/
module sanity_tb (
	clk,
	out
);
	input clk;
	output out;
syntaxerror
	wire clk;
	reg out;

	reg [31:0] sum = 0;

	always @(posedge clk) begin
		if(sum >= 21) begin
			out <= 1;
			sum <= 0;
		end else begin
			out <= 0;
			sum <= sum + 1;
		end
	end
endmodule
