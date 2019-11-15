/*
:name: forever_loop
:description: A module testing forever loop
:should_fail: 0
:tags: 12.7.6
*/
module foreach_tb ();
	initial begin
		fork
			forever begin : loop
				$display("loop");
			end : loop
			#100 disable loop;
		join
	end
endmodule
