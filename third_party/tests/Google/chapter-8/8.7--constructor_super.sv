// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: constructor_super
:description: class constructor super test
:tags: 8.7 8.17
*/
module class_tb ();
	class super_cls;
		int s = 2;
		function new(int def = 3);
			s = def;
		endfunction
	endclass
	class test_cls extends super_cls;
		int a;
		function new(int def = 42);
			super.new(def + 3);
			a = def;
		endfunction
	endclass

	test_cls test_obj;

	initial begin
		test_obj = new(37);

		$display(test_obj.a);
		$display(test_obj.s);
	end
endmodule
