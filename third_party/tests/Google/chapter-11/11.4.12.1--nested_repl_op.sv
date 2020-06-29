/*
:name: nested_repl_op
:description: nested replication operator test
:tags: 11.4.12.1
*/
module top();

bit [15:0] a;

bit [1:0] b = 2'b10;
bit [1:0] c = 2'b01;
bit [3:0] d = 4'b1111;

initial begin
	a = {{3{b, c}}, d};
end

endmodule
