/*
:name: assign_in_expr_inv
:description: invalid assignment in expression test
:should_fail_because: such assignment shall use parantheses to avoid confusion
:tags: 11.3.6
*/
module top();

int a;
int b;
int c;

initial begin
	a = b = c = 5;	
end

endmodule
