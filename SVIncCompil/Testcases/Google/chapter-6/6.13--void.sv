/*
:name: void
:description: void type tests
:should_fail: 0
:tags: 6.13
*/
module top();
	function void fun();
		$display("void fun");
	endfunction

	initial
		fun();
endmodule
