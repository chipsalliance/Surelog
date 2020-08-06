/*
:name: typedef_test_25__bad
:description: Test
:should_fail_because: A/D/E/M are not defined
:tags: 6.18
:type: simulation
*/

typedef struct packed {
  reg  [A-1:0] addr;
  reg [D-1:0] data;
`ifndef FOO
  reg  [E-1:0] ecc;
`endif //  `ifndef FOO
  reg   [M-1:0] mask;
  reg         parity;
} req_t;
