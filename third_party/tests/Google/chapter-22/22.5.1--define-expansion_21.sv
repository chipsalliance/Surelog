/*
:name: 22.5.1--define_expansion_21
:description: Test
:should_fail_because: invalid string declaration
:tags: 22.5.1
:type: preprocessing
*/
`define first_half "start of string
module top ();
initial $display(`first_half end of string");
endmodule
