/*
:name: arrays-packed-quering-functions-low
:description: Test quering functions support on packed arrays
:tags: 7.11 7.4.1
:type: simulation parsing
*/
module top ();

bit [7:0] arr;

initial begin
	$display(":assert: (%d == 0)", $low(arr));
end

endmodule
