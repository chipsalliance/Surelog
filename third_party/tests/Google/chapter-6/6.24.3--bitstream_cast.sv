/*
:name: bitstream_cast
:description: bitstream cast function
:tags: 6.24.3
*/
module top();
	struct packed {logic [7:0] a; logic [7:0] b; logic [15:0] c;} s;
	integer a = integer'(s);
endmodule
