/*
:name: 22.5.1--define_expansion_10
:description: Test
:tags: 22.5.1
:type: preprocessing
*/
`define MACRO1(a=5,b="B",c) initial $display(a,,b,,c);
module top ();
`MACRO1 ( 1 , , 3 )
endmodule
