/*
:name: size
:description: Test queues size support
:should_fail: 0
:tags: 7.10.2.1 7.10.2
*/
module top ();

int q[$];

initial begin
	$display(":assert: (%d == 0)", q.size);
end

endmodule
