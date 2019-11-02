/*
:name: jump_break
:description: A module testing break statement
:should_fail: 0
:tags: 12.8
*/
module jump_tb ();
	initial begin
		for (int i = 0; i < 256; i++)begin
			$display(i);
			if(i > 100)
				break;
		end

	end
endmodule
