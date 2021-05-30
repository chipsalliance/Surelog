// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: enum_sequence_range
:description: enum sequence range tests
:tags: 6.19.2
*/
module top();
	enum {start=10, stop[11:13]} e;
endmodule
