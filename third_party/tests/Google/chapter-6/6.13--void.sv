/*
:name: void
:description: void type tests
:should_fail: 0
:tags: 6.13
:type: simulation parsing
*/
module top();
	function void fun();
		$display(":assert:(True)");
	endfunction

	initial
		fun();
endmodule
