/*
:name: assign_in_expr
:description: assignment in expression test
:tags: 11.3.6
*/
module top();

int a;
int b;
int c;

initial begin
	a = (b = (c = 5));	
end

endmodule
