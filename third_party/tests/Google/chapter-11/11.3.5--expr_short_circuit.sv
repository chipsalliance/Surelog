/*
:name: expr_short_circuit
:description: expression short circuiting test
:tags: 11.3.5
*/
module top();

int a = 1;
int b;

function int fun1();
	$display("1");
	return 1;
endfunction

function int fun2();
	$display("2");
	return 2;
endfunction

initial begin
	b = (a > 0) ? fun1() : fun2();
end

endmodule
