// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: constraint_guards_0
:description: constraint guards test
:tags: 18.5.13
*/

class b;
    int d1;
endclass

class a;
    rand int b1;
    b next;

    constraint c1 { if (next == null) b1 == 5; }
endclass
