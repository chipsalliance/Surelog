/*
:name: preproc_test_13
:description: Test
:tags: 5.6.4
:type: preprocessing
*/
`define LONG_MACRO(
    a, b="(3,2)", c=(3,2)) \
a + b /c +345
