/*
:name: basic-tagged-union
:description: Test basic tagged union support
:should_fail: 0
:tags: 7.3.2
*/
module top ();

union tagged {
	void invalid;
	bit [3:0] valid;
} un;

initial begin
	un = tagged valid (10);
	$display(":assert: ('%p' == ''{valid:valid:10})'", un);
end

endmodule
