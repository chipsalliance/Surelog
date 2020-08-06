/*
:name: stream_concat
:description: stream concatenation test
:tags: 11.4.14.1
*/
module top();

int a = {"A", "B", "C", "D"};
int b = {"E", "F", "G", "H"};
logic [63:0] c;

initial begin
	c = {>> byte {a, b}};
end

endmodule
