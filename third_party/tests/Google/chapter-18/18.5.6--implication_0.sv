// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: implication_0
:description: implication test
:tags: 18.5.6
*/

class a;
    rand int b1, b2;
    constraint c1 { b1 == 5; }
    constraint c2 { b1 == 5 -> b2 == 10; }
endclass
