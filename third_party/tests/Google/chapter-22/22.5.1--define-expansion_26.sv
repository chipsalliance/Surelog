/*
:name: 22.5.1--define_expansion_26
:description: Test
:should_fail: 0
:tags: 22.5.1
:type: preprocessing
*/
`define append(f) f``_master
module top ();
$display(`append(clock));
endmodule
