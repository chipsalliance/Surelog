// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: mailbox_blocking
:description: blocking mailbox test
:tags: 15.4
*/
module top();

mailbox m;

initial begin
	m = new();
	string msg = "abc";
	string r;
	string r_peek;
	m.put(msg);
	m.peek(r_peek);
	$display(":assert: (%d == 1)", m.num());
	m.get(r);
	$display(":assert: ('%s' == '%s')", r, r_peek);
end

endmodule
