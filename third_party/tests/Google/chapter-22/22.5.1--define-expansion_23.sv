// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.5.1--define_expansion_23
:description: Test
:should_fail_because:  All compiler directives shall be considered predefined macro names; it shall be illegal to redefine a compiler directive as a macro name.
:tags: 22.5.1
:type: preprocessing
*/
`define define "illegal"
