// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.5.1--define_expansion_12
:description: Test
:should_fail_because: If fewer actual arguments are specified than the number of formal arguments and all the remaining formal arguments have defaults, then the defaults are substituted for the additional formal arguments. It shall be an error if any of the remaining formal arguments does not have a default specified.
:tags: 22.5.1
:type: preprocessing
*/
`define MACRO1(a=5,b="B",c) initial $display(a,,b,,c);
module top ();
`MACRO1 ( 1 ) // ILLEGAL: b and c omitted, no default for c
endmodule
