/*
:name: 22.5.1--define_expansion_9
:description: Test
:should_fail: 0
:tags: 22.5.1
:type: preprocessing
*/
`define MACRO1(a=5,b="B",c) $display(a,,b,,c)
module top ();
`MACRO1 ( , 2, 3 )
endmodule
