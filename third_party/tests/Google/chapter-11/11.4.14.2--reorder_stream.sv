/*
:name: reorder_stream
:description: stream reordering test
:tags: 11.4.14.2
*/
module top();

int a = {"A", "B", "C", "D"};
int b;

initial begin
	b = { << byte {a}};
end

endmodule
