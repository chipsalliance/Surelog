/*
:name: arrays-packed-quering-functions-left
:description: Test quering functions support on packed arrays
:should_fail: 0
:tags: 7.11 7.4.1
*/
module top ();

bit [7:0] arr;

initial begin
	$display(":assert: (%d == 7)", $left(arr));
end

endmodule
