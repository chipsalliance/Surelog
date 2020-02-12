/*
:name: 22.5.1--define_expansion_12
:description: Test
:should_fail: 1
:tags: 22.5.1
:type: preprocessing
*/
`define MACRO1(a=5,b="B",c) initial $display(a,,b,,c);
module top ();
`MACRO1 ( 1 )
endmodule
