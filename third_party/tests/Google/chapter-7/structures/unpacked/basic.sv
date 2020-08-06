/*
:name: basic-unpacked-structures
:description: Test unpacked structures support
:tags: 7.2 7.1
:type: simulation parsing
*/
module top ();

struct {
	bit [3:0] lo;
	bit [3:0] hi;
} p1;

initial begin
	p1.lo = 4'h5;
	p1.hi = 4'ha;
	$display(":assert: (('%h' == 'a') and ('%h' == '5'))", p1.hi, p1.lo);
end

endmodule
