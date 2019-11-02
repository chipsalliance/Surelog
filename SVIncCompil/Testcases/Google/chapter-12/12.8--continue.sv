/*
:name: jump_continue
:description: A module testing continue statement
:should_fail: 0
:tags: 12.8
*/
module jump_tb ();
	initial begin
		for (int i = 0; i < 256; i++)begin
			if(i < 100)
				continue;
			$display(i);
		end

	end
endmodule
