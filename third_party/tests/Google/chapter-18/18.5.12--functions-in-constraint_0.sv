// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: functions_in_constraints_0
:description: functions in constraints test
:tags: 18.5.12
*/

class a;
    rand int b1, b2;
    function int F (input int d);
        F=d;
    endfunction

    constraint c1 { b1 == 5; }
    constraint c2 { b2 == F(b1); }
endclass
