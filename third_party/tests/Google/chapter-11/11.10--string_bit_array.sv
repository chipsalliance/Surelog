/*
:name: string_bit_array
:description: string stored in bit array test
:tags: 11.10
*/
module top();

bit [8*14:1] a;

initial begin
	a = "Test";
end

endmodule
