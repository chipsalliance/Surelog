/*
:name: function_void_return
:description: void function return value test
:should_fail_because: void function shall not return a value
:tags: 13.4.1
:type: simulation
*/
module top();

function void add(int a, int b);
	$display("%d+%d=", a, b);
	return a + b;
endfunction

initial
	$display("%d", add(45, 90));

endmodule
