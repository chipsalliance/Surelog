// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: instance_constant
:description: class with instance constant variable
:tags: 8.19
*/
module class_tb ();
	class a_cls;
		const int c;
		function new(int val);
			c = 20 * val;
		endfunction
	endclass
endmodule
