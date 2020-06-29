/*
:name: void
:description: void type tests
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
