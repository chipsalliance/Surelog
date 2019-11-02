/*
:name: basic-packed-unions
:description: Test basic union support
:should_fail: 0
:tags: 7.3.1
*/
module top ();

union packed {
	bit [7:0] v1;
	bit [7:0] v2;
} un;

initial begin
	un.v1 = 8'd140;
	$display(":assert: (%d == 140)", un.v1);
	$display(":assert: (%d == 140)", un.v2);
end

endmodule
