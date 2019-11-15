/*
:name: jump_return
:description: A module testing return statement
:should_fail: 0
:tags: 12.8
*/
module jump_tb ();
	function void fun(input int a);
		$display("a");
		if(a == 21)
			return;
		$display(a);
		return;
	endfunction
	initial begin
		for (int i = 0; i < 256; i++)begin
			fun(i);
		end
	end
endmodule
