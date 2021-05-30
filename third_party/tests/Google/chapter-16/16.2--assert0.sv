// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: assert0_test
:description: assert #0 test
:tags: 16.4
*/
module top();

logic a = 1;

assert #0 (a != 0);

endmodule
