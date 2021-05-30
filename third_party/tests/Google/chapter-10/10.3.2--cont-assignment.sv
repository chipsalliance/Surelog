// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: cont_assignment
:description: continuous assignment test
:tags: 10.3.2
*/
module top(input a, input b);

wire w;
assign w = a & b;

endmodule
