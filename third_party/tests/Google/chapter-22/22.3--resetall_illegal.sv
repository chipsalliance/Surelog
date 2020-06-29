/*
:name: 22.3--resetall_illegal
:description: `resetall directive test
:should_fail_because: it shall be illegal for the `resetall directive to be specified within a design element
:tags: 22.3
:type: preprocessing parsing
*/
`resetall
module top ();
`resetall
endmodule
