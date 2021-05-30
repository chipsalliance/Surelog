// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: task
:description: task test
:tags: 13.3
:type: simulation parsing
*/
module top();

task mytask;
	$display(":assert: True");
endtask

initial 
	mytask;

endmodule
