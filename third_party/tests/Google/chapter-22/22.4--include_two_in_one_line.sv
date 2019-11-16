/*
:name: 22.4--include_two_in_one_line
:description: Test
:should_fail: 1
:tags: 22.4
:type: preprocessing parsing
*/
`include <dummy_include.sv> `include <dummy_include.sv>
module top ();
endmodule
