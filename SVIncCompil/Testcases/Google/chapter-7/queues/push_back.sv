/*
:name: push_back
:description: Test queues push_back function support
:should_fail: 0
:tags: 7.10.2.7 7.10.2
*/
module top ();

int q[$];

initial begin
	q.push_back(4);
	q.push_back(3);
	q.push_back(2);
	$display(":assert: (%d == 3)", q.size);
	$display(":assert: (%d == 4)", q[0]);
end

endmodule
