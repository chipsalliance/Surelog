// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: typedef_test_13
:description: Test
:tags: 6.18
*/
typedef bit data_t;
parameter k = 6;
parameter j = 5;
parameter l = 2;

typedef data_t my_ar_t [bit[31:0][k:0]][bit[j:0][l:0]];

module test;
endmodule
