// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: post_randomize_method_0
:description: post_randomize() method test
:tags: 18.6.2
*/

class a;
    rand int b;
    int d;

    constraint c { b == 5; }
    function void post_randomize();
        d = 20;
    endfunction
endclass
