/*
:name: typedef_test_26
:description: Test
:tags: 6.18
*/
typedef enum {
`ifdef TWO
  Global = 4'h2,
`else
  Global = 4'h1,
`endif
  Local = 4'h3
} myenum_fwd;