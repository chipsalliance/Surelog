/*
:name: jump_return_expr
:description: A module testing return <expr> statement
:tags: 12.8
*/
module jump_tb ();
	function int fun(input int a);
		return a * 3;
	endfunction
	initial begin
		for (int i = 0; i < 256; i++)begin
			$display(fun(i));
		end
	end
endmodule
