// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: parameters
:description: parametrized class test
:tags: 8.5 8.25
:type: simulation parsing
*/
module class_tb ();
	class test_cls #(parameter a = 12);
	endclass

	test_cls #(34) test_obj;

	initial begin
		test_obj = new;
		$display(":assert:(%d == 34)", test_obj.a);
	end
endmodule
