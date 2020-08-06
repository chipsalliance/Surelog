/*
:name: size
:description: Test queues size support
:tags: 7.10.2.1 7.10.2
:type: simulation parsing
*/
module top ();

int q[$];

initial begin
	$display(":assert: (%d == 0)", q.size);
end

endmodule
