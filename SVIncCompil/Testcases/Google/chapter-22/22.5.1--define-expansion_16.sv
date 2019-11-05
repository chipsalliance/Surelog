/*
:name: 22.5.1--define_expansion_16
:description: Test
:should_fail: 0
:tags: 22.5.1
:type: preprocessing
*/
`define MACRO3(a=5, b=0, c="C") $display(a,,b,,c);
module top ();
`MACRO3 ( 1 )
endmodule
