/*
:name: associative-arrays-literals
:description: Test associative arrays literals support
:tags: 7.9.11 7.8
:type: simulation parsing
*/
module top ();

string words [int] = '{default: "hello"};

initial begin
	$display(":assert: ('%s' == 'hello')", words[1]);
	words[1] = "world";
	$display(":assert: (('%s' == 'hello') and ('%s' == 'world'))",
		words[0], words[1]);
end

endmodule
