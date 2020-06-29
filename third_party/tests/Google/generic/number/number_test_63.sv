/*
:name: number_test_63
:description: hex literal test
:should_fail_because: hex literal with invalid leading underscore prefix should fail
:tags: 5.6.4 5.7.1 5.7.2
*/
parameter int foo = 32'H_7f_FF_;
