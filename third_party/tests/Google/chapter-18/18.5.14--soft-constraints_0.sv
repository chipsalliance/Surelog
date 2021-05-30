// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: soft_constraints_0
:description: soft constraints test
:tags: 18.5.14
*/


class a;
    rand int b;

    constraint c {
        soft b > 4;
        soft b < 12; }
endclass
