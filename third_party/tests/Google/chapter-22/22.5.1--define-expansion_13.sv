// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.5.1--define_expansion_13
:description: Test
:tags: 22.5.1
:type: preprocessing
*/
`define MACRO2(a=5, b, c="C") initial $display(a,,b,,c);
module top ();
`MACRO2 (1, , 3)
endmodule
