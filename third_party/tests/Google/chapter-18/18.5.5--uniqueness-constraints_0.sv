// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: uniqueness_constraints_0
:description: uniqueness constraints test
:tags: 18.5.5
*/

class a;
    rand int b1, b2;
    constraint c1 { b1 inside {3, 10}; }
    constraint c2 { b2 inside {3, 10}; }
    constraint c3 { unique {b1, b2}; }
endclass
