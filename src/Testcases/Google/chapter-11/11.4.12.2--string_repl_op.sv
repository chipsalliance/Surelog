/*
:name: string_repl_op
:description: string replication operator test
:should_fail: 0
:tags: 11.4.12.2
:type: simulation parsing
*/
module top();

string str;

initial begin
	str = {4{"test"}};
	$display(":assert:('%s' == 'testtesttesttest')", str);
end

endmodule
