// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: pure_constraint_0
:description: pure constraint test
:tags: 18.5.2
*/

virtual class a;
    pure constraint c;
endclass

class a2 extends a;
    rand int b2;
    constraint c { b2 == 5; }
endclass
