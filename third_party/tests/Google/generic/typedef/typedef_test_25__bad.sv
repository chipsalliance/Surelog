// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: typedef_test_25__bad
:description: Test
:should_fail_because: Using undefined parameters
:tags: 6.18
:type: simulation
*/

// A/D/E/M are not defined, so bad test.

typedef struct packed {
  reg  [A-1:0] addr;
  reg [D-1:0] data;
`ifndef FOO
  reg  [E-1:0] ecc;
`endif //  `ifndef FOO
  reg   [M-1:0] mask;
  reg         parity;
} req_t;

module test;
endmodule
