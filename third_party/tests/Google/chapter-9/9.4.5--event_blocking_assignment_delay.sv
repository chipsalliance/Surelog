/*
:name: event_blocking_assignment_delay
:description: event blk assignment delay
:tags: 9.4.5
*/
module block_tb ();
	reg a = 0;
	reg b = 1;

	initial begin
		a = #10 b;
	end
endmodule
