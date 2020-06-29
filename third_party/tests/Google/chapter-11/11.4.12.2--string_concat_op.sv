/*
:name: string_concat_op
:description: string concatenation operator test
:tags: 11.4.12.2
:type: simulation parsing
*/
module top();

string str;

initial begin
	str = {"Hello", "_", "World", "!"};
	$display(":assert:('%s' == 'Hello_World!')", str);
end

endmodule
