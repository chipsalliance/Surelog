/*
:name: 22.5.1--define_expansion_24
:description: Test
:tags: 22.5.1
:type: preprocessing
*/
module top ();
`define HI Hello
`define LO "`HI, world"
`define H(x) "Hello, x"
initial begin
	$display("`HI, world");
	$display(`LO);
	$display(`H(world));
end
endmodule
