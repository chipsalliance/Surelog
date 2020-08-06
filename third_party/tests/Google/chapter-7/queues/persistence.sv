/*
:name: queues-elements-persistence
:description: Test status of persistence of references to elements of queue
:tags: 7.10.3
:type: simulation parsing
*/
module top ();

int q[$];

task automatic fun(ref int e);
	$display(":assert: (%d == 2)", e);
	#100
	e = 10;
	$display(":assert: (%d == 10)", e);
endtask

initial begin
	q = { 1, 2, 3 };
	$display(":assert: ((%d == 1) and (%d == 2) and (%d == 3))",
		q[0], q[1], q[2]);
	fun(q[1]);
end

initial begin
	#50
	$display(":assert: (%d == 2)", q[1]);
	q = {};
	#100;
	$display(":assert: (%d == 0)", q.size);
end

endmodule
