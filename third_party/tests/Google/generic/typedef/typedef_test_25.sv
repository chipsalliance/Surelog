/*
:name: typedef_test_25
:description: Test
:should_fail: 0
:tags: 6.18
*/
parameter A = 5;
parameter D = 32;
parameter E = 7;
parameter M = 4;

typedef struct packed {
  reg  [A-1:0] addr;
  reg [D-1:0] data;
`ifndef FOO
  reg  [E-1:0] ecc;
`endif //  `ifndef FOO
  reg   [M-1:0] mask;
  reg         parity;
} req_t;
