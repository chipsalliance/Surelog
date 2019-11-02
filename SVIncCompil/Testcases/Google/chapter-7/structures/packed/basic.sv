/*
:name: basic-packed-structures
:description: Test packed structures support
:should_fail: 0
:tags: 7.2.1 7.2 7.1
*/
module top ();

struct packed {
	bit [3:0] lo;
	bit [3:0] hi;
} p1;

initial begin
	p1 = 8'h5a;
	$display(":assert: ('%h' == '5a')", p1);
	$display(":assert: (('%h' == 'a') and ('%h' == '5'))", p1.hi, p1.lo);
end

endmodule
