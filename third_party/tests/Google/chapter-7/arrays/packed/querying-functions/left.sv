/*
:name: arrays-packed-quering-functions-left
:description: Test quering functions support on packed arrays
:tags: 7.11 7.4.1
:type: simulation parsing
*/
module top ();

bit [7:0] arr;

initial begin
	$display(":assert: (%d == 7)", $left(arr));
end

endmodule
