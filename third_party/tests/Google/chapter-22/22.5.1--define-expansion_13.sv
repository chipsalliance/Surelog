/*
:name: 22.5.1--define_expansion_13
:description: Test
:should_fail: 0
:tags: 22.5.1
:type: preprocessing
*/
`define MACRO2(a=5, b, c="C") $display(a,,b,,c);
module top ();
`MACRO2 (1, , 3)
endmodule
