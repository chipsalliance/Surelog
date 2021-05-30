// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: const
:description: const test
:tags: 6.20.6
*/
module top();
	class test_cls;
		int a;
		task test_method(int val);
			$display("test_method");
			a += val;
		endtask
	endclass

	const test_cls test_obj = new;
endmodule
