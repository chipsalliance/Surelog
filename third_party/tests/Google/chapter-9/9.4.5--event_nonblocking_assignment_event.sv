/*
:name: event_nonblocking_assignment_event
:description: event non blk assignment event
:tags: 9.4.5
*/
module block_tb ();
	reg a = 0;
	reg b = 1;
	wire clk = 0;

	initial begin
		a = @(posedge clk) b;
	end
endmodule
