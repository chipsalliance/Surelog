/*
:name: typedef_test_18
:description: Test
:should_fail: 0
:tags: 6.18
*/
parameter K = 9;

typedef struct {
  rand bit i;
  randc integer b[K:0];
} randstruct;
