// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: cover_test
:description: cover test
:tags: 16.2
*/
module top();

logic a = 1;

initial cover (a != 0);

endmodule
