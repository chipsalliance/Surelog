/*
:name: delete
:description: Test queues delete function support
:tags: 7.10.2.3 7.10.2
:type: simulation parsing
*/
module top ();

int q[$];
int r;

initial begin
	q.push_back(2);
	q.push_back(3);
	q.push_back(4);
	$display(":assert: (%d == 3)", q.size);
	q.delete(0);
	$display(":assert: (%d == 2)", q.size);
	q.delete;
	$display(":assert: (%d == 0)", q.size);
end

endmodule
