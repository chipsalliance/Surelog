/*
:name: function_fork_valid
:description: function valid fork test
:tags: 13.4.4
:type: simulation parsing
*/
module top();

function int fun(int val);
	fork
		$display("abc");
		$display("def");
	join_none
	return val + 2;
endfunction

initial
	$display("$d", fun(2));

endmodule
