// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: package_ref
:description: package reference test
:tags: 26.3
:type: simulation parsing
*/

package mypkg;

function int add(int a, b);
	return a + b;
endfunction

endpackage : mypkg

module top();

initial $display(":assert: (%d == 4)", mypkg::add(1, 3));

endmodule
