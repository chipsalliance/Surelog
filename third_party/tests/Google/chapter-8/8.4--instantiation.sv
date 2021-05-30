// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: instantiation
:description: simple class instantiation test
:tags: 8.4
*/
module class_tb ();
	class test_cls;
		int a;
	endclass

	test_cls test_obj;

	initial begin
		if(test_obj == null) test_obj = new;
	end
endmodule
