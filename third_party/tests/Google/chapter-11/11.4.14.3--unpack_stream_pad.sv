/*
:name: unpack_stream_pad
:description: padded stream unpack test
:tags: 11.4.14.3
*/
module top();

int a = 1;
int b = 2;
int c = 3;

initial begin
	bit [127:0] d = {<<{a, b, c}};
end

endmodule
