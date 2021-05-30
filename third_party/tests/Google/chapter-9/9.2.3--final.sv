// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: final
:description: final check
:tags: 9.2.3
*/
module initial_tb ();
	reg a = 0;
	final
		a = 1;
endmodule
