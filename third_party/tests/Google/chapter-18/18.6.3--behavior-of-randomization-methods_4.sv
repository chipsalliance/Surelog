// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: behavior_of_randomization_methods_4
:description: behavior of randomization methods test
:should_fail_because: The randomize() method is built-in and cannot be overridden.
:tags: 18.6.3
:type: simulation
*/

class a;
    rand int b;
    constraint c { b > 5 && b < 12; }

    function void randomize();
        b = 7;
    endfunction
endclass
