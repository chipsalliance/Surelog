/*
:name: packed-and-unsigned-structures
:description: Test packed and unsigned structures support
:tags: 7.2.1 7.2
:type: simulation parsing
*/
module top ();

struct packed unsigned {
	bit [3:0] lo;
	bit [3:0] hi;
} p1;

initial begin
	p1 = 8'd200;
	$display(":assert: ('%h' == 'c8')", p1);
	$display(":assert: (%d == 200)", p1);
end

endmodule
