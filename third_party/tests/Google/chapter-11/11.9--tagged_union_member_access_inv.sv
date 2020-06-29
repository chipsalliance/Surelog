/*
:name: tagged_union_member_access_inv
:description: invalid tagged union member access test
:should_fail_because: invalid value cannot be accessed
:tags: 11.9
:type: simulation
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
	c = a.Valid;
end

endmodule
