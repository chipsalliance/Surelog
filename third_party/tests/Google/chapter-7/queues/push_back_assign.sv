/*
:name: push_back_assign
:description: Update queue by assignment (push_back)
:tags: 7.10.4
:type: simulation parsing
*/
module top ();

int q[$];

initial begin
	q = { q, 4 };
	q = { q, 3 };
	q = { q, 2 };
	$display(":assert: (%d == 3)", q.size);
	$display(":assert: (%d == 4)", q[0]);
end

endmodule
