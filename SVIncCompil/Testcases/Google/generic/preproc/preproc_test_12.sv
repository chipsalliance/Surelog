/*
:name: preproc_test_12
:description: Test
:should_fail: 0
:tags: 5.6.4
:type: preprocessing
*/
`define LONG_MACRO(
    a, b=2, c=42) \
a + b /c +345
