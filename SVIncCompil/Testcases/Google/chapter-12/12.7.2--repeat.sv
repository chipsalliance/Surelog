/*
:name: repeat_loop
:description: A module testing repeat loop
:should_fail: 0
:tags: 12.7.2
*/
module repeat_tb ();
	int a = 128;
	initial begin
		repeat(a)
			$display("repeat");
	end
endmodule
