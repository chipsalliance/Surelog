// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: always
:description: always check
:tags: 9.2.2.1 9.4.1
*/
module always_tb ();
	logic a = 0;
	always #5 a = ~a;
endmodule
