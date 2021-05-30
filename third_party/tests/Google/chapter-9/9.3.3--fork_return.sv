// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: fork_return
:description: illegal return from fork
:should_fail_because: illegal return from fork
:tags: 9.3.3
:type: simulation
*/
module block_tb ();
	task fork_test;
		fork
			#20;
			return;
		join_none
	endtask
endmodule
