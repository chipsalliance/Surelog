/*
:name: for_loop
:description: A module testing for loop
:should_fail: 0
:tags: 12.7.1
*/
module for_tb ();
	initial begin
		for (int i = 0; i < 256; i++)
			$display("%d", i);
	end
endmodule
