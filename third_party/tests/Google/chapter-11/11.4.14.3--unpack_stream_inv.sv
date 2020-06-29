/*
:name: unpack_stream_inv
:description: invalid stream unpack test
:should_fail_because: 96 bit stream will not fit in 32 bit variable d
:tags: 11.4.14.3
:type: simulation
*/
module top();

int a = 1;
int b = 2;
int c = 3;

initial begin
	int d = {<<{a, b, c}};
end

endmodule
