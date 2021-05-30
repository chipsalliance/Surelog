// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: distribution_0
:description: distribution test
:tags: 18.5.4
*/

class a;
    rand int b;
    constraint c { b dist {3 := 1, 10 := 2}; }
endclass
