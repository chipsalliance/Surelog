/*
:name: basic-tagged-packed-union
:description: Test tagged packed union support
:tags: 7.3.2
:type: simulation parsing
*/
module top ();

union tagged packed {
	bit [6:0] v1;
	bit [6:0] v2;
} un;

initial begin
    un = tagged v2 (10);
	un = tagged v1 (85); // 101_0101
	$display(":assert: ('%b' == 'v1:1010101'", un);
end

endmodule
