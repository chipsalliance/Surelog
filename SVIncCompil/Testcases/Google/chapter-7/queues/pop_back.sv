/*
:name: pop_back
:description: Test queues pop_back function support
:should_fail: 0
:tags: 7.10.2.5 7.10.2
*/
module top ();

int q[$];
int r;

initial begin
	q.push_back(2);
	q.push_back(3);
	q.push_back(4);
	r = q.pop_back;
	$display(":assert: (%d == 2)", q.size);
	$display(":assert: (%d == 4)", r);
end

endmodule
