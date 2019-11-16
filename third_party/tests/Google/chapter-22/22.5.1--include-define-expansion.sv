/*
:name: 22.5.1--include-define-expansion
:description: Test
:should_fail: 0
:tags: 22.5.1
:type: preprocessing parsing
*/
`define foo(the_file) `"the_file`"
`include `foo(dummy_include.sv)
