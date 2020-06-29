/*
:name: package_decl
:description: package declaration test
:tags: 26.2
*/
module top();

endmodule

package mypkg;

function int add(int a, b);
	return a + b;
endfunction

endpackage : mypkg
