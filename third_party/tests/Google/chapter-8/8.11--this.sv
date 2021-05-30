// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: this
:description: this keyword test
:tags: 8.11
*/
module class_tb ();
	class test_cls;
		int a;
		task test_method(int a);
			$display("test_method");
			this.a += a;
		endtask
	endclass
endmodule
