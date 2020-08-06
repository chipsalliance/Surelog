/*
:name: pop_front
:description: Test queues pop_front function support
:tags: 7.10.2.4 7.10.2
:type: simulation parsing
*/
module top ();

int q[$];
int r;

initial begin
	q.push_back(2);
	q.push_back(3);
	q.push_back(4);
	r = q.pop_front;
	$display(":assert: (%d == 2)", q.size);
	$display(":assert: (%d == 2)", r);
end

endmodule
