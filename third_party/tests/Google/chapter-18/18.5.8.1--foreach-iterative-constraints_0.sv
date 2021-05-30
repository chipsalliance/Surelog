// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: foreach_iterative_constraints_0
:description: foreach iterative constraints test
:tags: 18.5.8.1
*/

class a;
    rand int B[5];
    constraint c { foreach ( B [ i ] ) B[i] == 5; }
endclass
