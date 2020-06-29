/*
:name: 22.5.1--define_expansion_15
:description: Test
:tags: 22.5.1
:type: preprocessing
*/
`define MACRO2(a=5, b, c="C") initial $display(a,,b,,c);
module top ();
`MACRO2 (, 2)
endmodule
