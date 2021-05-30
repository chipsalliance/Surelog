// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: manually_seeding_randomize_0
:description: manually seeding randomize test
:tags: 18.15
*/

class a;
    rand int x;
    function new (int seed);
        this.srandom(seed);
    endfunction
endclass
