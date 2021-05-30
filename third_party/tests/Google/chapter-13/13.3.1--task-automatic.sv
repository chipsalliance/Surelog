// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: task_automatic
:description: automatic task test
:tags: 13.3.1
:type: simulation parsing
*/
module top();

task automatic mytask;
	int a = 0;
	a++;
	$display(":assert:(%d == 1)", a);
endtask

initial begin
   mytask;
   mytask;
   mytask;
   mytask;
end

endmodule
