// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: typedef_test_28
:description: Test
:should_fail_because: missing forward typedef declaration, type_identifier does not resolve to a data type.
:tags: 6.18
:type: simulation
*/

// 6.18 says:
// The actual data type definition of a forward typedef declaration shall
// be resolved within the same localscope or generate block. It shall be an
// error if the type_identifier does not resolve to a data type.

typedef missing_forward_typedef;

module test;
endmodule
