/*
:name: wait_fork
:description: wait fork test
:tags: 9.6.1
*/
module fork_tb ();
	reg a = 0;
	reg b = 0;
	initial begin
		fork
			begin
				#50 a = 1;
				#50 a = 0;
				#50 a = 1;
			end
			begin
				#50 b = 1;
				#50 b = 0;
				#50 b = 1;
			end
		join_none
		wait fork;
	end
endmodule
