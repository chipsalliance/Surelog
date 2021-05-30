// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: typedef_test_8__bad
:description: Test
:should_fail_because: defining a type using an undefined type
:tags: 6.18
:type: simulation
*/
// some_other_type is not defined
typedef some_other_type myalias;

module test;
endmodule
