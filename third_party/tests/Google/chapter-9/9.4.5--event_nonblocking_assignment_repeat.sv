/*
:name: event_nonblocking_assignment_repeat
:description: event non blk assignment repeat
:tags: 9.4.5
*/
module block_tb ();
	reg a = 0;
	reg b = 1;
	wire clk = 0;

	initial begin
		a = repeat(3) @(posedge clk) b;
	end
endmodule
