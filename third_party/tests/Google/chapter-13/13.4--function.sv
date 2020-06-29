/*
:name: function
:description: function test
:tags: 13.4
:type: simulation parsing
*/
module top();

function int test(int val);
	return val + 1;
endfunction

initial
	$display(":assert: (%d == 2)", test(1));

endmodule
