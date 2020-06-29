/*
:name: 22.4--include_two_in_one_line
:description: Test
:should_fail_because: only white space or a comment may appear on the same line as the `include compiler directive
:tags: 22.4
:type: preprocessing parsing
*/
`include <dummy_include.sv> `include <dummy_include.sv>
module top ();
endmodule
