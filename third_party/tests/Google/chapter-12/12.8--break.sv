/*
:name: jump_break
:description: A module testing break statement
:tags: 12.8
:type: simulation parsing
*/
module jump_tb ();
	initial begin
		int i;
		for (i = 0; i < 256; i++)begin
			if(i > 100)
				break;
		end
		$display(":assert:(%d == 101)", i);
	end
endmodule
