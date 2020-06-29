/*
:name: push_front
:description: Test queues push_front function support
:tags: 7.10.2.6 7.10.2
:type: simulation parsing
*/
module top ();

int q[$];

initial begin
	q.push_front(2);
	q.push_front(3);
	q.push_front(4);
	$display(":assert: (%d == 3)", q.size);
	$display(":assert: (%d == 4)", q[0]);
end

endmodule
