/*
:name: unpack_stream_inv
:description: invalid stream unpack test
:should_fail: 1
:tags: 11.4.14.3
*/
module top();

int a = 1;
int b = 2;
int c = 3;

initial begin
	int d = {<<{a, b, c}};
end

endmodule
