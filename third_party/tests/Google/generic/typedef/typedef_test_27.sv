// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: typedef_test_27
:description: Test
:tags: 6.18
*/
typedef enum {
  Global = 2,
`ifdef TWO
  Local = 2
`else
  Local = 1
`endif
} myenum_fwd;

module test;
endmodule
