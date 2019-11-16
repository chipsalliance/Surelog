module tb (input clock, a, b);
	wire x, y;

	top top_inst (
		.clock(clock),
		.a(a), .b(b), .x(x), .y(y)
	);

	always @(posedge clock) begin
		assert (x == ($past(a, 2) ^ $past(b, 2)));
		assert (y == (!$past(a, 2) || !$past(b, 2)));
	end
endmodule
