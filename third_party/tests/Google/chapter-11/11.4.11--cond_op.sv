/*
:name: cond_op
:description: ?: operator test
:tags: 11.4.11
*/
module top();

int a = 12;
int b = 5;
int c;

initial begin
	c = (a > b) ? 11 : 13;
end

endmodule
