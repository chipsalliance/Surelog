/*
:name: function_fork_invalid
:description: function invalid fork test
:should_fail_because: a function shall not contain any time-controlled statements
:tags: 13.4.4
:type: simulation
*/
module top();

function int fun(int val);
	fork
		$display("abc");
		$display("def");
	join_any
	return val + 2;
endfunction

initial
	$display("$d", fun(2));

endmodule
