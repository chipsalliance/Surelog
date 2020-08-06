/*
:name: insert
:description: Test queues insert function support
:tags: 7.10.2.2 7.10.2
:type: simulation parsing
*/
module top ();

int q[$];

initial begin
	q.insert(0, 1);
	$display(":assert: (%d == 1)", q.size);
	$display(":assert: (%d == 1)", q[0]);
end

endmodule
