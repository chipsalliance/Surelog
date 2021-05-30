// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.5.3--undefineall-and-redefine
:description: Test
:tags: 22.5.3
:type: preprocessing
*/
`define FOO "foo"
`undefineall
`define FOO 5
`undefineall
`define FOO(x,y) (x + y)
