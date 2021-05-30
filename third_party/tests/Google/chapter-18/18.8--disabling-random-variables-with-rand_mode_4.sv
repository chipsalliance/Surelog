// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: disabling-random-variables-with-rand_mode_4
:description: rand_mode() test
:should_fail_because: The rand_mode() method is built-in and cannot be overridden.
:tags: 18.8
:type: simulation
*/

class a1;
    rand int x;
    function int rand_mode();
        return 1;
    endfunction
endclass
