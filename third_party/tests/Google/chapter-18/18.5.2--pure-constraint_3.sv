// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: pure_constraint_3
:description: pure constraint test
:tags: 18.5.2
*/

virtual class a;
    pure constraint c;
endclass

virtual class a2 extends a;
endclass
