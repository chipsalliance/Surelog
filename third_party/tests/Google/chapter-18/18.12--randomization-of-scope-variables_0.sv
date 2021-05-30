// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: randomization_of_scope_variables_0
:description: Randomization of scope variables - std::randomize() test
:tags: 18.12
*/

class a;
    function int do_randomize();
        int x, success;
        success = std::randomize(x);
        return success;
    endfunction
endclass
