// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: in-line_constraints--randomize_3
:description: in-line constraints test - randomize()
:tags: 18.7
*/

class a;
    rand int x;
endclass

function int F(a obj, int y);
    F = obj.randomize() with (x) { x > 0; x < y; };
endfunction
