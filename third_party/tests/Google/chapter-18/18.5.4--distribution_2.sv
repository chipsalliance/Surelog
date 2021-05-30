// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: distribution_2
:description: distribution test
:should_fail_because: distribution shall not be applied to randc variables
:tags: 18.5.4
:type: simulation
*/

class a;
    randc int b;
    constraint c { b dist {3 := 0, 10 := 5}; }
endclass
