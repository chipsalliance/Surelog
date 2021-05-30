// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: string_substr
:description: string.substr()  tests
:tags: 6.16.8
*/
module top();
	string a = "Test";
	string b = a.substr(1, 2);
endmodule
