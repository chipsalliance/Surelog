/*
:name: pop_back-assign
:description: Update queue by assignment (pop_back)
:tags: 7.10.4
:type: simulation parsing
*/
module top ();

int q[$];
int r;

initial begin
	q = { 2, 3, 4 };
	r = q[$-1];
	q = q[0:$-1]; // void'(q.pop_back()) or q.delete(q.size-1)
	$display(":assert: (%d == 2)", q.size);
	$display(":assert: (%d == 4)", r);
end

endmodule
