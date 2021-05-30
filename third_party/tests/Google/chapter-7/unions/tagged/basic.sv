// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: basic-tagged-union
:description: Test basic tagged union support
:tags: 7.3.2
:type: simulation parsing
*/
module top ();

union tagged {
	void invalid;
	bit [3:0] valid;
} un;

initial begin
	un = tagged valid (10);
	$display(":assert: ('%p' == ''{valid:valid:10})'", un);
end

endmodule
