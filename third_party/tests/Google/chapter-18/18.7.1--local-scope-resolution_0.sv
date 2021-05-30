// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: local_scope_resolution_0
:description: local:: scope resolution test
:tags: 18.7.1
*/

class a;
    rand int x;
endclass

function int F(a obj, int x);
    F = obj.randomize() with {x < local::x; };
endfunction
