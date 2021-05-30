// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: typedef_test_18
:description: Test
:tags: 6.18
*/
parameter K = 9;

typedef struct {
  rand bit i;
  randc integer b[K:0];
} randstruct;

module test;
endmodule
