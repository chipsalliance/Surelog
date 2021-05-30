// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: string_compare_fn
:description: string.compare()  tests
:tags: 6.16.6
*/
module top();
	string a = "Test";
	string b = "TEST";
	int c = a.compare(b);
endmodule
