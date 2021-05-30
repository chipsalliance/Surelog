// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: size
:description: Test queues size support
:tags: 7.10.2.1 7.10.2
:type: simulation parsing
*/
module top ();

int q[$];

initial begin
	$display(":assert: (%d == 0)", q.size);
end

endmodule
