// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: pure_constraint_2
:description: pure constraint test
:should_fail_because: pure constraint must be implemented by non-virtual class
:tags: 18.5.2
:type: simulation
*/

virtual class a;
    pure constraint c;
endclass

class a2 extends a;
endclass
