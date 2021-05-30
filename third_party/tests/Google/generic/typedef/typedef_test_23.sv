// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: typedef_test_23
:description: Test
:tags: 6.18
*/
typedef bit[3:0] num_t;
typedef enum num_t {
  Global = 4'h2,
  Local = 4'h3
} myenum_fwd;

module test;
endmodule
