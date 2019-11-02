/*
:name: push_front_assign
:description: Update queue by assignment (push_front)
:should_fail: 0
:tags: 7.10.4
*/
module top ();

int q[$];

initial begin
	q = { 2, q };
	q = { 3, q };
	q = { 4, q };
	$display(":assert: (%d == 3)", q.size);
	$display(":assert: (%d == 4)", q[0]);
end

endmodule
