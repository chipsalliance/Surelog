/*
:name: unpack_stream
:description: stream unpack test
:tags: 11.4.14.3
*/
module top();

int a = 1;
int b = 2;
int c = 3;

initial begin
	bit [95:0] d = {<<{a, b, c}};
end

endmodule
