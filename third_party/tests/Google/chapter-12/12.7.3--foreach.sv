// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: foreach_loop
:description: A module testing foreach loop
:tags: 12.7.3
*/
module foreach_tb ();
	string test [4] = '{"111", "222", "333", "444"};
	initial begin
		foreach(test[i])
			$display(i, test[i]);
	end
endmodule
