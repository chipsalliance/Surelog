// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: explicit_external_constraint_1
:description: explicit external constraint test
:should_fail_because: explicit contraint needs to be defined
:tags: 18.5.1
:type: simulation
*/

class a;
    rand int b;
    extern constraint c;
endclass
