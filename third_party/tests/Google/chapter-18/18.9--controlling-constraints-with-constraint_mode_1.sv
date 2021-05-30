// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: controlling_constraints_with_constraint_mode_1
:description: constraint_mode() test
:should_fail_because: The constraint_mode() method is built-in and cannot be overridden.
:tags: 18.8
:type: simulation
*/

class a;
    rand int x;
    function int constraint_mode();
        return 1;
    endfunction
endclass
