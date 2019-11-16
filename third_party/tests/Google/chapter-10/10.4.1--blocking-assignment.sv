/*
:name: blocking_assignment
:description: blocking assignment test
:should_fail: 0
:tags: 10.4.1
:type: simulation parsing
*/
module top();

logic a = 3;
logic b = 2;

initial begin
	a = 1;
	b = a;
	$display(":assert: (%d == %d)", a, b);
end

endmodule
