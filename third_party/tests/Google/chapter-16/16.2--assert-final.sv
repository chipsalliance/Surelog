// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: assert_final_test
:description: assert final test
:tags: 16.4
*/
module top();

logic a = 1;

assert final (a != 0);

endmodule
