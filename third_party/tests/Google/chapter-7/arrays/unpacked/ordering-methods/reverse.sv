// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: ordering-methods-reverse
:description: Test support of reverse method on unpacked arrays
:tags: 7.12.2 7.4.2
:type: simulation parsing
*/
module top ();

string s[] = { "hello", "sad", "world" };

initial begin
	$display(":assert: (('%s' == 'hello') and ('%s' == 'sad') and ('%s' == 'world'))",
		s[0], s[1], s[2]);
	s.reverse;
	$display(":assert: (('%s' == 'world') and ('%s' == 'sad') and ('%s' == 'hello'))",
		s[0], s[1], s[2]);
end

endmodule
