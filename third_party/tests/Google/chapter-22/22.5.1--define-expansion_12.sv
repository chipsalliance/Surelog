/*
:name: 22.5.1--define_expansion_12
:description: Test
:should_fail_because: b and c arguments are omitted and there's no default for c
:tags: 22.5.1
:type: preprocessing
*/
`define MACRO1(a=5,b="B",c) initial $display(a,,b,,c);
module top ();
`MACRO1 ( 1 )
endmodule
