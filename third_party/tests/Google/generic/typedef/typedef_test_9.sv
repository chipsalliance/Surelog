// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: typedef_test_9
:description: Test
:tags: 6.18
*/
parameter j = 3;
parameter k = 2;
typedef bit data_t;

typedef data_t my_array_t [k:0][j:0];

module test;
endmodule
