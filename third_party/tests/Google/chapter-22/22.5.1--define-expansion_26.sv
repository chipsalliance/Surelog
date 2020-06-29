/*
:name: 22.5.1--define_expansion_26
:description: Test
:tags: 22.5.1
:type: preprocessing
*/
`define append(f) f``_master
module top ();
initial $display(`append(clock));
endmodule
