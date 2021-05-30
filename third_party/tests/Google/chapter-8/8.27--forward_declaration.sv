// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: forward_declaration
:description: class forward declaration test
:tags: 8.27
*/
module class_tb ();
	typedef class C2;

	class C1;
		C2 c;
	endclass

	class C2;
		C1 c;
	endclass
endmodule
