/*
:name: unpacked-structures-members-default-value
:description: Test unpacked structures members default value support
:tags: 7.2.2
:type: simulation parsing
*/
module top ();

parameter c = 4'h5;

struct {
	bit [3:0] lo = c;
	bit [3:0] hi;
} p1;

initial begin
	p1.hi = 4'ha;
	$display(":assert: (('%h' == 'a') and ('%h' == '5'))", p1.hi, p1.lo);
end

endmodule
