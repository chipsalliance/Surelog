/*
:name: string_repl_op
:description: string replication operator test
:should_fail: 0
:tags: 11.4.12.2
*/
module top();

string str;

initial begin
	str = {4{"test "}};
	$display(str);
end

endmodule
