/*
:name: string_concat_op
:description: string concatenation operator test
:should_fail: 0
:tags: 11.4.12.2
*/
module top();

string str;

initial begin
	str = {"Hello", " ", "World", "!"};
	$display(str);
end

endmodule
