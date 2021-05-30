// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: task_static
:description: static task test
:tags: 13.3.1
:type: simulation parsing
*/
module top();

task static mytask(int test);
	int a = 0;
	a++;
	if (test)
		$display(":assert:(%d != 1)", a);
	else
		$display(":assert:(%d == 1)", a);
endtask

initial
	begin
		mytask(0);
		mytask(1);
		mytask(1);
		mytask(1);
	end

endmodule
