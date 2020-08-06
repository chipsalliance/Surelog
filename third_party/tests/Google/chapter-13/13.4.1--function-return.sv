/*
:name: function_return
:description: function return value test
:tags: 13.4.1
:type: simulation parsing
*/
module top();

function int add(int a, int b);
	return a + b;
endfunction

initial
	$display(":assert: (%d == 90)", add(30, 60));

endmodule
