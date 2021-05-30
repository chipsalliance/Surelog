// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: typedef_test_26
:description: Test
:tags: 6.18
*/
typedef enum {
`ifdef TWO
  Global = 2,
`else
  Global = 1,
`endif
  Local = 3
} myenum_fwd;

module test;
endmodule
