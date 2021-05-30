// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.5.1--define_expansion_8
:description: Test
:should_fail_because: It shall be an error to specify more actual arguments than the number of formal arguments.
:tags: 22.5.1
:type: preprocessing
*/
`define D(x,y) initial $display("start", x , y, "end");
`D(,,)
