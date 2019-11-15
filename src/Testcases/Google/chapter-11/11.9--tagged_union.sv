/*
:name: tagged_union
:description: tagged union test
:should_fail: 0
:tags: 11.9
*/
module top();

typedef union tagged {
	void Invalid;
	int Valid;
} u_int;

u_int a, b;

initial begin
	a = tagged Invalid;
	b = tagged Valid(42);
end

endmodule
