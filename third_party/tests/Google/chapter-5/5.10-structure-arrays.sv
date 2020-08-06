/*
:name: structure-arrays
:description: Structure array assignment tests
:tags: 5.10
*/
module top();
  typedef struct {
    int a;
    int b;
  } ms_t;

  ms_t ms[1:0] = '{'{0, 0}, '{1, 1}};

endmodule
