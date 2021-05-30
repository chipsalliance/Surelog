// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.5.1--define_expansion_9
:description: Test
:tags: 22.5.1
:type: preprocessing
*/
`define MACRO1(a=5,b="B",c) initial $display(a,,b,,c);
module top ();
`MACRO1 ( , 2, 3 )
endmodule
