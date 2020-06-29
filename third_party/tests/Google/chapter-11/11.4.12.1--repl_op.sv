/*
:name: repl_op
:description: replication operator test
:tags: 11.4.12.1
*/
module top();

bit [15:0] a;

bit [1:0] b = 2'b10;

initial begin
	a = {8{b}};
end

endmodule
