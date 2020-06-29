/*
:name: empty_string
:description: empty string test
:tags: 11.10.3
*/
module top();

bit [8*14:1] a;

initial begin
	a = "";
	assert(a == 0);
end

endmodule
