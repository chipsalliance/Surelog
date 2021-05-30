// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: cast_func
:description: $cast function test
:tags: 8.16
*/
module class_tb ();
	typedef enum { aaa, bbb, ccc, ddd, eee } values;
	initial begin
		values val;
		if(!$cast(val, 5))
			$display("$cast failed");
		$display(val);
	end
endmodule
