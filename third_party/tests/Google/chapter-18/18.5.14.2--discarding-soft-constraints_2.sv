// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: discarding_soft_constraints_2
:description: discarding soft constraints test
:tags: 18.5.14.2
*/


class a;
    rand int b;

    constraint c1 {
        soft b > 4;
        soft b < 12; }

    constraint c2 { disable soft b; soft b == 20; }
endclass
