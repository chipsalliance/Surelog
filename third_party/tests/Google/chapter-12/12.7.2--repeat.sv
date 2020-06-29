/*
:name: repeat_loop
:description: A module testing repeat loop
:tags: 12.7.2
*/
module repeat_tb ();
	int a = 128;
	initial begin
		repeat(a)
			$display("repeat");
	end
endmodule
