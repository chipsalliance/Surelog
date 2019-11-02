/*
:name: unary_op_inc
:description: ++ operator test
:should_fail: 0
:tags: 11.4.2
*/
module top();

int a = 12;

initial begin
	a++;
end

endmodule
