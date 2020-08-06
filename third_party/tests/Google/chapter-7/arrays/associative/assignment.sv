/*
:name: associative-arrays-assignment
:description: Test associative arrays assignment support
:tags: 7.9.9 7.8
:type: simulation parsing
*/
module top ();

string words [ int ];
string w [ int ];

initial begin
	words[0] = "hello";
	words[1] = "happy";
	words[2] = "world";
	$display(":assert: (('%s' == 'hello') and ('%s' == 'happy') and ('%s' == 'world'))",
		words[0], words[1], words[2]);

	w = words;
	w[1] = "sad";

	$display(":assert: (('%s' == 'hello') and ('%s' == 'happy') and ('%s' == 'world'))",
		words[0], words[1], words[2]);
	$display(":assert: (('%s' == 'hello') and ('%s' == 'sad') and ('%s' == 'world'))",
		w[0], w[1], w[2]);
end

endmodule
