/*
:name: jump_continue
:description: A module testing continue statement
:tags: 12.8
:type: simulation parsing
*/
module jump_tb ();
	initial begin
		for (int i = 0; i < 256; i++)begin
			if(i < 255)
				continue;
			$display(":assert:(%d == 255)", i);
		end

	end
endmodule
