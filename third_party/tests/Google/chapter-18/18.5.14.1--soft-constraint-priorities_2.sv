// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: soft_constraint_priorities_2
:description: soft constraint priorities test
:tags: 18.5.14.1
*/


class a1;
    rand int b;

    constraint c1 {
        soft b > 4;
        soft b < 12; }
endclass

class a2 extends a1;
    constraint c2 { soft b == 20; }
    constraint c3;
endclass

constraint a2::c3 { soft b > 100; };
