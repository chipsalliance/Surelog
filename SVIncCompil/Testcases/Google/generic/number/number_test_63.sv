/*
:name: number_test_63
:description: Hex literal with invalid leading underscore prefix should fail.
:should_fail: 1
:tags: 5.6.4 5.7.1 5.7.2
*/
parameter int foo = 32'H_7f_FF_;
