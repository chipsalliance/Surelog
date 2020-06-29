/*
:name: 22.5.1--include-define-expansion
:description: Test
:tags: 22.5.1
:type: preprocessing
*/
`define foo(the_file) `"the_file`"
`include `foo(dummy_include.sv)
