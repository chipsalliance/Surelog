/*
:name: package_ref
:description: package reference test
:should_fail: 0
:tags: 26.3
:type: simulation parsing
*/

package mypkg;

function int add(int a, b);
	return a + b;
endfunction

endpackage : mypkg

module top();

initial $display(":assert: (%d == 4)", mypkg::add(1, 3));

endmodule
