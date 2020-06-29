/*
:name: const_function
:description: const function test
:tags: 13.4.3
:type: simulation parsing
*/
module top();

localparam a = fun(3);

function int fun(int val);
	return val + 1;
endfunction

initial
	$display(":assert: (%d == 4)", a);

endmodule
