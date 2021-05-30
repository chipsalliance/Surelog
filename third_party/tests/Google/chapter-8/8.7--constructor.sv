// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: constructor
:description: class constructor test
:tags: 8.7
:type: simulation parsing
*/
module class_tb ();
	class test_cls;
		int a;
		function new();
			a = 42;
		endfunction
	endclass

	initial begin
		test_cls test_obj = new;

		$display(":assert:(%d == 42)", test_obj.a);
	end
endmodule
