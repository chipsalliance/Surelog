// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: parametrized_class_extend
:description: parametrized class extending another parametrized class
:tags: 8.25
*/
module class_tb ();
	class base_cls #(int b = 20);
		int a;
	endclass

	class ext_cls #(int e = 25) extends base_cls #(5);
		int c;
	endclass

	ext_cls #(15) inst;

	initial begin
		inst = new;
	end
endmodule
