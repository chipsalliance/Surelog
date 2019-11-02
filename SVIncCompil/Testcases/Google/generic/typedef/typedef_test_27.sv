/*
:name: typedef_test_27
:description: Test
:should_fail: 0
:tags: 6.18
*/
typedef enum {
  Global = 4'h2,
`ifdef TWO
  Local = 4'h2
`else
  Local = 4'h1
`endif
} myenum_fwd;