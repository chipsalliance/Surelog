// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: parametrized_class_scope_resolution
:description: parametrized class scope resolution
:tags: 8.25.1
*/
module class_tb ();

	class par_cls #(int a = 25);
		parameter int b = 23;
	endclass

	par_cls #(15) inst;

	initial begin
		inst = new;

		$display(par_cls#()::b);
	end
endmodule
