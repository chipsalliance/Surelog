/*
:name: tagged_union_member_access
:description: tagged union member access test
:tags: 11.9
*/
module top();

typedef union tagged {
	void Invalid;
	int Valid;
} u_int;

u_int a, b;

int c;

initial begin
	a = tagged Invalid;
	b = tagged Valid(42);
	c = b.Valid;
end

endmodule
