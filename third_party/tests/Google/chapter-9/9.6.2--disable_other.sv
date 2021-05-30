// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: disable_other
:description: disable other task
:tags: 9.6.2
*/
module fork_tb ();
	reg a = 0;
	reg b = 0;
	reg c = 0;
	initial fork
		begin: block
			#10 a = 1;
			#10 b = 1;
		end
		#15 disable block;
	join
endmodule
