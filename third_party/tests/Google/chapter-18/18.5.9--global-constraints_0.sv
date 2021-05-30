// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: global_constraints_0
:description: global constraints test
:tags: 18.5.9
*/

class a;
    rand int v;
endclass

class b;
    rand a aObj;
    rand int v;

    constraint c { aObj.v < v; }
endclass
