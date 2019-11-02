/*
:name: structure-arrays-illegal
:description: Structure array assignment tests
:should_fail: 1
:tags: 5.10
*/
module top();
  typedef struct {
    int a;
    int b;
  } ms_t;

  /* C-like assignment is illegal */
  ms_t ms[1:0] = '{0, 0, 1, 1};

endmodule
