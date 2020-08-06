/*
:name: delete-assign
:description: Update queue by assignment (delete)
:tags: 7.10.4
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
	q = q[1:$]; // q.delete(0)
	$display(":assert: (%d == 2)", q.size);
	q = {}; // q.delete
	$display(":assert: (%d == 0)", q.size);
end

endmodule
