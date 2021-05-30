// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: constraint_inheritance_0
:description: contraint inheritance test
:tags: 18.5.2
*/

class a;
    rand int b;
    constraint c { b == 5; };
endclass

class a2 extends a;
    rand int b2;
    constraint c2 { b2 == b; }
endclass
