// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: scope_resolution
:description: access static method using scope resolution operator
:tags: 8.23
*/
module class_tb ();
	class test_cls;
		static int id = 0;
		static function int next_id();
			++id;
			next_id = id;
		endfunction
	endclass

	initial begin
		$display(test_cls::next_id());
		$display(test_cls::next_id());
	end
endmodule
