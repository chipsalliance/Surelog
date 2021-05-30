// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: set_membership_0
:description: set membership test
:tags: 18.5.3
*/

class a;
    rand int b;
    constraint c { b inside {3, 10}; }
endclass
